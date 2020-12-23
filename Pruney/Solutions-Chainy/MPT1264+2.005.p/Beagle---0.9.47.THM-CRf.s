%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:39 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 203 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 465 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :   10 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_80,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_119,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [B_41] : k9_subset_1(k2_struct_0('#skF_1'),B_41,'#skF_2') = k3_xboole_0(B_41,'#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_119])).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_138,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28])).

tff(c_26,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_88,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_83,c_88])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [B_41] : k9_subset_1(k2_struct_0('#skF_1'),B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_119])).

tff(c_148,plain,(
    ! [A_45,C_46,B_47] :
      ( k9_subset_1(A_45,C_46,B_47) = k9_subset_1(A_45,B_47,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [B_47] : k9_subset_1(k2_struct_0('#skF_1'),B_47,'#skF_3') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_47) ),
    inference(resolution,[status(thm)],[c_83,c_148])).

tff(c_157,plain,(
    ! [B_47] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_3',B_47) = k3_xboole_0(B_47,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_152])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v1_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_214,plain,(
    ! [A_50,B_51] :
      ( k2_pre_topc(A_50,B_51) = k2_struct_0(A_50)
      | ~ v1_tops_1(B_51,A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_221,plain,(
    ! [B_51] :
      ( k2_pre_topc('#skF_1',B_51) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_51,'#skF_1')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_214])).

tff(c_243,plain,(
    ! [B_58] :
      ( k2_pre_topc('#skF_1',B_58) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_58,'#skF_1')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_221])).

tff(c_253,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_243])).

tff(c_258,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_253])).

tff(c_328,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_pre_topc(A_68,k9_subset_1(u1_struct_0(A_68),B_69,k2_pre_topc(A_68,C_70))) = k2_pre_topc(A_68,k9_subset_1(u1_struct_0(A_68),B_69,C_70))
      | ~ v3_pre_topc(B_69,A_68)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_343,plain,(
    ! [B_69] :
      ( k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),B_69,'#skF_2'))
      | ~ v3_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_328])).

tff(c_353,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_1',k9_subset_1(k2_struct_0('#skF_1'),B_71,k2_struct_0('#skF_1'))) = k2_pre_topc('#skF_1',k3_xboole_0(B_71,'#skF_2'))
      | ~ v3_pre_topc(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_80,c_82,c_80,c_128,c_80,c_80,c_343])).

tff(c_366,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0(k2_struct_0('#skF_1'),'#skF_3')) = k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_353])).

tff(c_376,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_26,c_101,c_2,c_366])).

tff(c_378,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:13:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.30  %$ v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.19/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.30  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.19/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.19/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.19/1.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.19/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.19/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.30  
% 2.19/1.32  tff(f_91, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tops_1)).
% 2.19/1.32  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.19/1.32  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.19/1.32  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.19/1.32  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.19/1.32  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.19/1.32  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.19/1.32  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.19/1.32  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_1)).
% 2.19/1.32  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.32  tff(c_71, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.32  tff(c_76, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_16, c_71])).
% 2.19/1.32  tff(c_80, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.19/1.32  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_82, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_32])).
% 2.19/1.32  tff(c_119, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.32  tff(c_128, plain, (![B_41]: (k9_subset_1(k2_struct_0('#skF_1'), B_41, '#skF_2')=k3_xboole_0(B_41, '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_119])).
% 2.19/1.32  tff(c_24, plain, (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_81, plain, (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24])).
% 2.19/1.32  tff(c_138, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_81])).
% 2.19/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_83, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28])).
% 2.19/1.32  tff(c_26, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_88, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.32  tff(c_95, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_83, c_88])).
% 2.19/1.32  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.32  tff(c_101, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_95, c_4])).
% 2.19/1.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.32  tff(c_127, plain, (![B_41]: (k9_subset_1(k2_struct_0('#skF_1'), B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_83, c_119])).
% 2.19/1.32  tff(c_148, plain, (![A_45, C_46, B_47]: (k9_subset_1(A_45, C_46, B_47)=k9_subset_1(A_45, B_47, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.32  tff(c_152, plain, (![B_47]: (k9_subset_1(k2_struct_0('#skF_1'), B_47, '#skF_3')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_47))), inference(resolution, [status(thm)], [c_83, c_148])).
% 2.19/1.32  tff(c_157, plain, (![B_47]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_3', B_47)=k3_xboole_0(B_47, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_152])).
% 2.19/1.32  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_30, plain, (v1_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.19/1.32  tff(c_214, plain, (![A_50, B_51]: (k2_pre_topc(A_50, B_51)=k2_struct_0(A_50) | ~v1_tops_1(B_51, A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.32  tff(c_221, plain, (![B_51]: (k2_pre_topc('#skF_1', B_51)=k2_struct_0('#skF_1') | ~v1_tops_1(B_51, '#skF_1') | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_214])).
% 2.19/1.32  tff(c_243, plain, (![B_58]: (k2_pre_topc('#skF_1', B_58)=k2_struct_0('#skF_1') | ~v1_tops_1(B_58, '#skF_1') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_221])).
% 2.19/1.32  tff(c_253, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_243])).
% 2.19/1.32  tff(c_258, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_253])).
% 2.19/1.32  tff(c_328, plain, (![A_68, B_69, C_70]: (k2_pre_topc(A_68, k9_subset_1(u1_struct_0(A_68), B_69, k2_pre_topc(A_68, C_70)))=k2_pre_topc(A_68, k9_subset_1(u1_struct_0(A_68), B_69, C_70)) | ~v3_pre_topc(B_69, A_68) | ~m1_subset_1(C_70, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.32  tff(c_343, plain, (![B_69]: (k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), B_69, '#skF_2')) | ~v3_pre_topc(B_69, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_328])).
% 2.19/1.32  tff(c_353, plain, (![B_71]: (k2_pre_topc('#skF_1', k9_subset_1(k2_struct_0('#skF_1'), B_71, k2_struct_0('#skF_1')))=k2_pre_topc('#skF_1', k3_xboole_0(B_71, '#skF_2')) | ~v3_pre_topc(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_80, c_82, c_80, c_128, c_80, c_80, c_343])).
% 2.19/1.32  tff(c_366, plain, (k2_pre_topc('#skF_1', k3_xboole_0(k2_struct_0('#skF_1'), '#skF_3'))=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_157, c_353])).
% 2.19/1.32  tff(c_376, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_26, c_101, c_2, c_366])).
% 2.19/1.32  tff(c_378, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_376])).
% 2.19/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  Inference rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Ref     : 0
% 2.19/1.32  #Sup     : 76
% 2.19/1.32  #Fact    : 0
% 2.19/1.32  #Define  : 0
% 2.19/1.32  #Split   : 1
% 2.19/1.32  #Chain   : 0
% 2.19/1.32  #Close   : 0
% 2.19/1.32  
% 2.19/1.32  Ordering : KBO
% 2.19/1.32  
% 2.19/1.32  Simplification rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Subsume      : 8
% 2.19/1.32  #Demod        : 50
% 2.19/1.32  #Tautology    : 40
% 2.19/1.32  #SimpNegUnit  : 3
% 2.19/1.32  #BackRed      : 4
% 2.19/1.32  
% 2.19/1.32  #Partial instantiations: 0
% 2.19/1.32  #Strategies tried      : 1
% 2.19/1.32  
% 2.19/1.32  Timing (in seconds)
% 2.19/1.32  ----------------------
% 2.19/1.32  Preprocessing        : 0.31
% 2.19/1.32  Parsing              : 0.16
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.24
% 2.19/1.32  Inferencing          : 0.09
% 2.19/1.32  Reduction            : 0.08
% 2.19/1.32  Demodulation         : 0.06
% 2.19/1.32  BG Simplification    : 0.02
% 2.19/1.32  Subsumption          : 0.03
% 2.19/1.32  Abstraction          : 0.02
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.58
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
