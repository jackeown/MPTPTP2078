%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 127 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 197 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_78,plain,(
    ! [A_29] :
      ( m1_subset_1(k2_struct_0(A_29),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_78])).

tff(c_82,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_90,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = k2_subset_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_subset_1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_36,plain,(
    ! [A_5] : k3_subset_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_173,plain,(
    ! [B_44,A_45] :
      ( v4_pre_topc(B_44,A_45)
      | ~ v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_183,plain,(
    ! [A_45] :
      ( v4_pre_topc(k1_xboole_0,A_45)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_189,plain,(
    ! [A_45] :
      ( v4_pre_topc(k1_xboole_0,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_183])).

tff(c_158,plain,(
    ! [A_42,B_43] :
      ( k2_pre_topc(A_42,B_43) = B_43
      | ~ v4_pre_topc(B_43,A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_191,plain,(
    ! [A_47] :
      ( k2_pre_topc(A_47,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_196,plain,(
    ! [A_48] :
      ( k2_pre_topc(A_48,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_189,c_191])).

tff(c_199,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_196])).

tff(c_202,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_199])).

tff(c_92,plain,(
    ! [A_30,B_31] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_6] : k3_subset_1(A_6,k3_subset_1(A_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_99,plain,(
    ! [A_6] : k3_subset_1(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_96])).

tff(c_292,plain,(
    ! [A_58,B_59] :
      ( k3_subset_1(u1_struct_0(A_58),k2_pre_topc(A_58,k3_subset_1(u1_struct_0(A_58),B_59))) = k1_tops_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_314,plain,(
    ! [B_59] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_59))) = k1_tops_1('#skF_1',B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_292])).

tff(c_357,plain,(
    ! [B_61] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_61))) = k1_tops_1('#skF_1',B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_73,c_73,c_314])).

tff(c_376,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_357])).

tff(c_384,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_36,c_202,c_376])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.82  
% 3.05/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.82  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 3.05/1.82  
% 3.05/1.82  %Foreground sorts:
% 3.05/1.82  
% 3.05/1.82  
% 3.05/1.82  %Background operators:
% 3.05/1.82  
% 3.05/1.82  
% 3.05/1.82  %Foreground operators:
% 3.05/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.05/1.82  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.05/1.82  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.05/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.05/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.82  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.05/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.05/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.05/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.05/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.82  
% 3.09/1.84  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.09/1.84  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.09/1.84  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.09/1.84  tff(f_63, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.09/1.84  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.09/1.84  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.09/1.84  tff(f_36, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.09/1.84  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.09/1.84  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.09/1.84  tff(f_55, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.09/1.84  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.09/1.84  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.09/1.84  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.09/1.84  tff(c_30, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.84  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.84  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.09/1.84  tff(c_64, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.09/1.84  tff(c_69, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_22, c_64])).
% 3.09/1.84  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_69])).
% 3.09/1.84  tff(c_78, plain, (![A_29]: (m1_subset_1(k2_struct_0(A_29), k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.09/1.84  tff(c_81, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_78])).
% 3.09/1.84  tff(c_82, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_81])).
% 3.09/1.84  tff(c_85, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_82])).
% 3.09/1.84  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_85])).
% 3.09/1.84  tff(c_90, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_81])).
% 3.09/1.84  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.09/1.84  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.09/1.84  tff(c_10, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=k2_subset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.84  tff(c_35, plain, (![A_5]: (k3_subset_1(A_5, k1_subset_1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 3.09/1.84  tff(c_36, plain, (![A_5]: (k3_subset_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_35])).
% 3.09/1.84  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.09/1.84  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.09/1.84  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.09/1.84  tff(c_173, plain, (![B_44, A_45]: (v4_pre_topc(B_44, A_45) | ~v1_xboole_0(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.09/1.84  tff(c_183, plain, (![A_45]: (v4_pre_topc(k1_xboole_0, A_45) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(resolution, [status(thm)], [c_12, c_173])).
% 3.09/1.84  tff(c_189, plain, (![A_45]: (v4_pre_topc(k1_xboole_0, A_45) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_183])).
% 3.09/1.84  tff(c_158, plain, (![A_42, B_43]: (k2_pre_topc(A_42, B_43)=B_43 | ~v4_pre_topc(B_43, A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.09/1.84  tff(c_191, plain, (![A_47]: (k2_pre_topc(A_47, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_12, c_158])).
% 3.09/1.84  tff(c_196, plain, (![A_48]: (k2_pre_topc(A_48, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(resolution, [status(thm)], [c_189, c_191])).
% 3.09/1.84  tff(c_199, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_196])).
% 3.09/1.84  tff(c_202, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_199])).
% 3.09/1.84  tff(c_92, plain, (![A_30, B_31]: (k3_subset_1(A_30, k3_subset_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.09/1.84  tff(c_96, plain, (![A_6]: (k3_subset_1(A_6, k3_subset_1(A_6, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_92])).
% 3.09/1.84  tff(c_99, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_96])).
% 3.09/1.84  tff(c_292, plain, (![A_58, B_59]: (k3_subset_1(u1_struct_0(A_58), k2_pre_topc(A_58, k3_subset_1(u1_struct_0(A_58), B_59)))=k1_tops_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.09/1.84  tff(c_314, plain, (![B_59]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_59)))=k1_tops_1('#skF_1', B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_292])).
% 3.09/1.84  tff(c_357, plain, (![B_61]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_61)))=k1_tops_1('#skF_1', B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_73, c_73, c_314])).
% 3.09/1.84  tff(c_376, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_99, c_357])).
% 3.09/1.84  tff(c_384, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_36, c_202, c_376])).
% 3.09/1.84  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_384])).
% 3.09/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.84  
% 3.09/1.84  Inference rules
% 3.09/1.84  ----------------------
% 3.09/1.84  #Ref     : 0
% 3.09/1.84  #Sup     : 74
% 3.09/1.84  #Fact    : 0
% 3.09/1.84  #Define  : 0
% 3.09/1.84  #Split   : 3
% 3.09/1.84  #Chain   : 0
% 3.09/1.84  #Close   : 0
% 3.09/1.84  
% 3.09/1.84  Ordering : KBO
% 3.09/1.84  
% 3.09/1.84  Simplification rules
% 3.09/1.84  ----------------------
% 3.09/1.84  #Subsume      : 3
% 3.09/1.84  #Demod        : 50
% 3.09/1.84  #Tautology    : 33
% 3.09/1.84  #SimpNegUnit  : 2
% 3.09/1.84  #BackRed      : 0
% 3.09/1.84  
% 3.09/1.84  #Partial instantiations: 0
% 3.09/1.84  #Strategies tried      : 1
% 3.09/1.84  
% 3.09/1.84  Timing (in seconds)
% 3.09/1.84  ----------------------
% 3.09/1.85  Preprocessing        : 0.50
% 3.09/1.85  Parsing              : 0.26
% 3.09/1.85  CNF conversion       : 0.03
% 3.09/1.85  Main loop            : 0.41
% 3.09/1.85  Inferencing          : 0.16
% 3.09/1.85  Reduction            : 0.12
% 3.09/1.85  Demodulation         : 0.09
% 3.09/1.85  BG Simplification    : 0.02
% 3.09/1.85  Subsumption          : 0.06
% 3.09/1.85  Abstraction          : 0.02
% 3.09/1.85  MUC search           : 0.00
% 3.09/1.85  Cooper               : 0.00
% 3.09/1.85  Total                : 0.96
% 3.09/1.85  Index Insertion      : 0.00
% 3.09/1.85  Index Deletion       : 0.00
% 3.09/1.85  Index Matching       : 0.00
% 3.09/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
