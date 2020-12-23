%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:41 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 270 expanded)
%              Number of leaves         :   28 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 658 expanded)
%              Number of equality atoms :   32 ( 158 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_14,c_36])).

tff(c_45,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_30])).

tff(c_84,plain,(
    ! [A_35,B_36,C_37] :
      ( k9_subset_1(A_35,B_36,C_37) = k3_xboole_0(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [B_36] : k9_subset_1(k2_struct_0('#skF_1'),B_36,'#skF_2') = k3_xboole_0(B_36,'#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_84])).

tff(c_22,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_22])).

tff(c_103,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_46])).

tff(c_24,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_26])).

tff(c_53,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_67,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_67])).

tff(c_28,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_314,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = k2_struct_0(A_61)
      | ~ v1_tops_1(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_324,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_1',B_62) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_62,'#skF_1')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_314])).

tff(c_329,plain,(
    ! [B_63] :
      ( k2_pre_topc('#skF_1',B_63) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_324])).

tff(c_342,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_329])).

tff(c_350,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_342])).

tff(c_113,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(k2_pre_topc(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [B_41] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_41),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_113])).

tff(c_135,plain,(
    ! [B_45] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_45),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_45,c_121])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( k9_subset_1(A_3,B_4,C_5) = k3_xboole_0(B_4,C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    ! [B_47,B_48] :
      ( k9_subset_1(k2_struct_0('#skF_1'),B_47,k2_pre_topc('#skF_1',B_48)) = k3_xboole_0(B_47,k2_pre_topc('#skF_1',B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_135,c_4])).

tff(c_164,plain,(
    ! [B_47] : k9_subset_1(k2_struct_0('#skF_1'),B_47,k2_pre_topc('#skF_1','#skF_2')) = k3_xboole_0(B_47,k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_151])).

tff(c_396,plain,(
    ! [B_47] : k9_subset_1(k2_struct_0('#skF_1'),B_47,k2_struct_0('#skF_1')) = k3_xboole_0(B_47,k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_350,c_164])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_351,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_pre_topc(A_64,k9_subset_1(u1_struct_0(A_64),B_65,k2_pre_topc(A_64,C_66))) = k2_pre_topc(A_64,k9_subset_1(u1_struct_0(A_64),B_65,C_66))
      | ~ v3_pre_topc(B_65,A_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_384,plain,(
    ! [B_65,C_66] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_65,k2_pre_topc('#skF_1',C_66))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_65,C_66))
      | ~ v3_pre_topc(B_65,'#skF_1')
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_351])).

tff(c_562,plain,(
    ! [B_76,C_77] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_76,k2_pre_topc('#skF_1',C_77))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_76,C_77))
      | ~ v3_pre_topc(B_76,'#skF_1')
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_45,c_45,c_45,c_384])).

tff(c_600,plain,(
    ! [B_76] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_76,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_76,'#skF_2'))
      | ~ v3_pre_topc(B_76,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_562])).

tff(c_934,plain,(
    ! [B_97] :
      ( k2_pre_topc('#skF_1',k3_xboole_0(B_97,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_97,'#skF_2'))
      | ~ v3_pre_topc(B_97,'#skF_1')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_396,c_93,c_600])).

tff(c_947,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3',k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_934])).

tff(c_957,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_75,c_947])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.48  
% 3.18/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.48  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.48  
% 3.18/1.48  %Foreground sorts:
% 3.18/1.48  
% 3.18/1.48  
% 3.18/1.48  %Background operators:
% 3.18/1.48  
% 3.18/1.48  
% 3.18/1.48  %Foreground operators:
% 3.18/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.18/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.48  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.18/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.18/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.18/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.18/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.18/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.18/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.48  
% 3.18/1.49  tff(f_91, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 3.18/1.49  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.18/1.49  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.18/1.49  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.18/1.49  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.49  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.18/1.49  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 3.18/1.49  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.18/1.49  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 3.18/1.49  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.49  tff(c_36, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.49  tff(c_41, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_14, c_36])).
% 3.18/1.49  tff(c_45, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_41])).
% 3.18/1.49  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_47, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_30])).
% 3.18/1.49  tff(c_84, plain, (![A_35, B_36, C_37]: (k9_subset_1(A_35, B_36, C_37)=k3_xboole_0(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.49  tff(c_93, plain, (![B_36]: (k9_subset_1(k2_struct_0('#skF_1'), B_36, '#skF_2')=k3_xboole_0(B_36, '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_84])).
% 3.18/1.49  tff(c_22, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_46, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_22])).
% 3.18/1.49  tff(c_103, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_46])).
% 3.18/1.49  tff(c_24, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_26])).
% 3.18/1.49  tff(c_53, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.49  tff(c_60, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_53])).
% 3.18/1.49  tff(c_67, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.49  tff(c_75, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_60, c_67])).
% 3.18/1.49  tff(c_28, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_314, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=k2_struct_0(A_61) | ~v1_tops_1(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.49  tff(c_324, plain, (![B_62]: (k2_pre_topc('#skF_1', B_62)=k2_struct_0('#skF_1') | ~v1_tops_1(B_62, '#skF_1') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_314])).
% 3.18/1.49  tff(c_329, plain, (![B_63]: (k2_pre_topc('#skF_1', B_63)=k2_struct_0('#skF_1') | ~v1_tops_1(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_324])).
% 3.18/1.49  tff(c_342, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_47, c_329])).
% 3.18/1.49  tff(c_350, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_342])).
% 3.18/1.49  tff(c_113, plain, (![A_40, B_41]: (m1_subset_1(k2_pre_topc(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.49  tff(c_121, plain, (![B_41]: (m1_subset_1(k2_pre_topc('#skF_1', B_41), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_113])).
% 3.18/1.49  tff(c_135, plain, (![B_45]: (m1_subset_1(k2_pre_topc('#skF_1', B_45), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_45, c_121])).
% 3.18/1.49  tff(c_4, plain, (![A_3, B_4, C_5]: (k9_subset_1(A_3, B_4, C_5)=k3_xboole_0(B_4, C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.49  tff(c_151, plain, (![B_47, B_48]: (k9_subset_1(k2_struct_0('#skF_1'), B_47, k2_pre_topc('#skF_1', B_48))=k3_xboole_0(B_47, k2_pre_topc('#skF_1', B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_135, c_4])).
% 3.18/1.49  tff(c_164, plain, (![B_47]: (k9_subset_1(k2_struct_0('#skF_1'), B_47, k2_pre_topc('#skF_1', '#skF_2'))=k3_xboole_0(B_47, k2_pre_topc('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_47, c_151])).
% 3.18/1.49  tff(c_396, plain, (![B_47]: (k9_subset_1(k2_struct_0('#skF_1'), B_47, k2_struct_0('#skF_1'))=k3_xboole_0(B_47, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_350, c_164])).
% 3.18/1.49  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.18/1.49  tff(c_351, plain, (![A_64, B_65, C_66]: (k2_pre_topc(A_64, k9_subset_1(u1_struct_0(A_64), B_65, k2_pre_topc(A_64, C_66)))=k2_pre_topc(A_64, k9_subset_1(u1_struct_0(A_64), B_65, C_66)) | ~v3_pre_topc(B_65, A_64) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.18/1.49  tff(c_384, plain, (![B_65, C_66]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_65, k2_pre_topc('#skF_1', C_66)))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_65, C_66)) | ~v3_pre_topc(B_65, '#skF_1') | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45, c_351])).
% 3.18/1.49  tff(c_562, plain, (![B_76, C_77]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_76, k2_pre_topc('#skF_1', C_77)))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_76, C_77)) | ~v3_pre_topc(B_76, '#skF_1') | ~m1_subset_1(C_77, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_45, c_45, c_45, c_384])).
% 3.18/1.49  tff(c_600, plain, (![B_76]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_76, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_76, '#skF_2')) | ~v3_pre_topc(B_76, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_350, c_562])).
% 3.18/1.49  tff(c_934, plain, (![B_97]: (k2_pre_topc('#skF_1', k3_xboole_0(B_97, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_97, '#skF_2')) | ~v3_pre_topc(B_97, '#skF_1') | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_396, c_93, c_600])).
% 3.18/1.49  tff(c_947, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_934])).
% 3.18/1.49  tff(c_957, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_75, c_947])).
% 3.18/1.49  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_957])).
% 3.18/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  Inference rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Ref     : 0
% 3.18/1.49  #Sup     : 204
% 3.18/1.49  #Fact    : 0
% 3.18/1.49  #Define  : 0
% 3.18/1.49  #Split   : 4
% 3.18/1.49  #Chain   : 0
% 3.18/1.49  #Close   : 0
% 3.18/1.49  
% 3.18/1.49  Ordering : KBO
% 3.18/1.49  
% 3.18/1.49  Simplification rules
% 3.18/1.49  ----------------------
% 3.18/1.49  #Subsume      : 28
% 3.18/1.49  #Demod        : 206
% 3.18/1.49  #Tautology    : 75
% 3.18/1.49  #SimpNegUnit  : 13
% 3.18/1.49  #BackRed      : 6
% 3.18/1.49  
% 3.18/1.49  #Partial instantiations: 0
% 3.18/1.49  #Strategies tried      : 1
% 3.18/1.49  
% 3.18/1.49  Timing (in seconds)
% 3.18/1.49  ----------------------
% 3.18/1.49  Preprocessing        : 0.31
% 3.18/1.50  Parsing              : 0.17
% 3.18/1.50  CNF conversion       : 0.02
% 3.18/1.50  Main loop            : 0.40
% 3.18/1.50  Inferencing          : 0.14
% 3.18/1.50  Reduction            : 0.14
% 3.18/1.50  Demodulation         : 0.10
% 3.18/1.50  BG Simplification    : 0.02
% 3.18/1.50  Subsumption          : 0.07
% 3.18/1.50  Abstraction          : 0.03
% 3.18/1.50  MUC search           : 0.00
% 3.18/1.50  Cooper               : 0.00
% 3.18/1.50  Total                : 0.75
% 3.18/1.50  Index Insertion      : 0.00
% 3.18/1.50  Index Deletion       : 0.00
% 3.18/1.50  Index Matching       : 0.00
% 3.18/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
