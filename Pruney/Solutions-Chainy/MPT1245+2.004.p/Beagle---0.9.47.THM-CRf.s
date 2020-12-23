%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:50 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 339 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 641 expanded)
%              Number of equality atoms :   34 ( 208 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
             => k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = k7_subset_1(u1_struct_0(A),k2_struct_0(A),B) )
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(c_24,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) != k2_pre_topc('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_25] :
      ( u1_struct_0(A_25) = k2_struct_0(A_25)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_52,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_80,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_53,c_80])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k3_subset_1(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_58])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_87,plain,(
    ! [A_32,B_33,C_34] :
      ( k7_subset_1(A_32,B_33,C_34) = k4_xboole_0(B_33,C_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_4,C_34] : k7_subset_1(A_4,A_4,C_34) = k4_xboole_0(A_4,C_34) ),
    inference(resolution,[status(thm)],[c_31,c_87])).

tff(c_195,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),B_45)) = k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),B_45)
      | ~ v3_pre_topc(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,(
    ! [B_45] :
      ( k2_pre_topc('#skF_1',k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_45)) = k7_subset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_45)
      | ~ v3_pre_topc(B_45,'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_195])).

tff(c_209,plain,(
    ! [B_46] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_46)) = k4_xboole_0(k2_struct_0('#skF_1'),B_46)
      | ~ v3_pre_topc(B_46,'#skF_1')
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52,c_93,c_93,c_52,c_204])).

tff(c_212,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_53,c_209])).

tff(c_219,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_65,c_65,c_212])).

tff(c_125,plain,(
    ! [A_39,B_40] :
      ( k3_subset_1(u1_struct_0(A_39),k2_pre_topc(A_39,k3_subset_1(u1_struct_0(A_39),B_40))) = k1_tops_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_144,plain,(
    ! [B_40] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_40))) = k1_tops_1('#skF_1',B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_125])).

tff(c_151,plain,(
    ! [B_40] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_40))) = k1_tops_1('#skF_1',B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52,c_52,c_144])).

tff(c_225,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_151])).

tff(c_229,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_85,c_225])).

tff(c_22,plain,(
    ! [A_18,B_20] :
      ( k2_pre_topc(A_18,k1_tops_1(A_18,k2_pre_topc(A_18,k1_tops_1(A_18,B_20)))) = k2_pre_topc(A_18,k1_tops_1(A_18,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_234,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_22])).

tff(c_238,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_53,c_52,c_229,c_234])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.33  %$ v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.24/1.33  
% 2.24/1.33  %Foreground sorts:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Background operators:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Foreground operators:
% 2.24/1.33  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.24/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.33  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.24/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.33  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.24/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.24/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.24/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.24/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.24/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.24/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.33  
% 2.24/1.35  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tops_1)).
% 2.24/1.35  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.24/1.35  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.24/1.35  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.24/1.35  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.24/1.35  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.24/1.35  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.24/1.35  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.24/1.35  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) => (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) & ((v2_pre_topc(A) & (k2_pre_topc(A, k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = k7_subset_1(u1_struct_0(A), k2_struct_0(A), B))) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_pre_topc)).
% 2.24/1.35  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.24/1.35  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 2.24/1.35  tff(c_24, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))!=k2_pre_topc('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.35  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.35  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.35  tff(c_43, plain, (![A_25]: (u1_struct_0(A_25)=k2_struct_0(A_25) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.24/1.35  tff(c_48, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_14, c_43])).
% 2.24/1.35  tff(c_52, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.24/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.35  tff(c_53, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 2.24/1.35  tff(c_80, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.35  tff(c_85, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_53, c_80])).
% 2.24/1.35  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.24/1.35  tff(c_58, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k3_subset_1(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.35  tff(c_65, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_53, c_58])).
% 2.24/1.35  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.35  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.35  tff(c_31, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 2.24/1.35  tff(c_87, plain, (![A_32, B_33, C_34]: (k7_subset_1(A_32, B_33, C_34)=k4_xboole_0(B_33, C_34) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.35  tff(c_93, plain, (![A_4, C_34]: (k7_subset_1(A_4, A_4, C_34)=k4_xboole_0(A_4, C_34))), inference(resolution, [status(thm)], [c_31, c_87])).
% 2.24/1.35  tff(c_195, plain, (![A_44, B_45]: (k2_pre_topc(A_44, k7_subset_1(u1_struct_0(A_44), k2_struct_0(A_44), B_45))=k7_subset_1(u1_struct_0(A_44), k2_struct_0(A_44), B_45) | ~v3_pre_topc(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.24/1.35  tff(c_204, plain, (![B_45]: (k2_pre_topc('#skF_1', k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_45))=k7_subset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_45) | ~v3_pre_topc(B_45, '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_195])).
% 2.24/1.35  tff(c_209, plain, (![B_46]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_46))=k4_xboole_0(k2_struct_0('#skF_1'), B_46) | ~v3_pre_topc(B_46, '#skF_1') | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52, c_93, c_93, c_52, c_204])).
% 2.24/1.35  tff(c_212, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_53, c_209])).
% 2.24/1.35  tff(c_219, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_65, c_65, c_212])).
% 2.24/1.35  tff(c_125, plain, (![A_39, B_40]: (k3_subset_1(u1_struct_0(A_39), k2_pre_topc(A_39, k3_subset_1(u1_struct_0(A_39), B_40)))=k1_tops_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.24/1.35  tff(c_144, plain, (![B_40]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_40)))=k1_tops_1('#skF_1', B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_125])).
% 2.24/1.35  tff(c_151, plain, (![B_40]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_40)))=k1_tops_1('#skF_1', B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52, c_52, c_144])).
% 2.24/1.35  tff(c_225, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_219, c_151])).
% 2.24/1.35  tff(c_229, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_85, c_225])).
% 2.24/1.35  tff(c_22, plain, (![A_18, B_20]: (k2_pre_topc(A_18, k1_tops_1(A_18, k2_pre_topc(A_18, k1_tops_1(A_18, B_20))))=k2_pre_topc(A_18, k1_tops_1(A_18, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.24/1.35  tff(c_234, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_229, c_22])).
% 2.24/1.35  tff(c_238, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_53, c_52, c_229, c_234])).
% 2.24/1.35  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_238])).
% 2.24/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  Inference rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Ref     : 0
% 2.24/1.35  #Sup     : 52
% 2.24/1.35  #Fact    : 0
% 2.24/1.35  #Define  : 0
% 2.24/1.35  #Split   : 2
% 2.24/1.35  #Chain   : 0
% 2.24/1.35  #Close   : 0
% 2.24/1.35  
% 2.24/1.35  Ordering : KBO
% 2.24/1.35  
% 2.24/1.35  Simplification rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Subsume      : 1
% 2.24/1.35  #Demod        : 24
% 2.24/1.35  #Tautology    : 29
% 2.24/1.35  #SimpNegUnit  : 1
% 2.24/1.35  #BackRed      : 1
% 2.24/1.35  
% 2.24/1.35  #Partial instantiations: 0
% 2.24/1.35  #Strategies tried      : 1
% 2.24/1.35  
% 2.24/1.35  Timing (in seconds)
% 2.24/1.35  ----------------------
% 2.24/1.35  Preprocessing        : 0.33
% 2.24/1.35  Parsing              : 0.19
% 2.24/1.35  CNF conversion       : 0.02
% 2.24/1.35  Main loop            : 0.19
% 2.24/1.35  Inferencing          : 0.07
% 2.24/1.35  Reduction            : 0.06
% 2.24/1.35  Demodulation         : 0.05
% 2.24/1.35  BG Simplification    : 0.01
% 2.24/1.35  Subsumption          : 0.03
% 2.24/1.35  Abstraction          : 0.01
% 2.24/1.35  MUC search           : 0.00
% 2.24/1.35  Cooper               : 0.00
% 2.24/1.35  Total                : 0.55
% 2.24/1.35  Index Insertion      : 0.00
% 2.24/1.35  Index Deletion       : 0.00
% 2.24/1.35  Index Matching       : 0.00
% 2.24/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
