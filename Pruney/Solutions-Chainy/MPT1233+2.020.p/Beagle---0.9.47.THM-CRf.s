%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 153 expanded)
%              Number of equality atoms :   30 (  55 expanded)
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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_28,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_80,axiom,(
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

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_4,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = k2_subset_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_subset_1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_37,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_115,plain,(
    ! [B_40,A_41] :
      ( v4_pre_topc(B_40,A_41)
      | ~ v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [B_40] :
      ( v4_pre_topc(B_40,'#skF_1')
      | ~ v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_115])).

tff(c_134,plain,(
    ! [B_43] :
      ( v4_pre_topc(B_43,'#skF_1')
      | ~ v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_118])).

tff(c_138,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_145,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_148,plain,(
    ! [A_44,B_45] :
      ( k2_pre_topc(A_44,B_45) = B_45
      | ~ v4_pre_topc(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,(
    ! [A_46] :
      ( k2_pre_topc(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_148])).

tff(c_167,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_164])).

tff(c_173,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_88,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [A_7] : k3_subset_1(A_7,k3_subset_1(A_7,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_94,plain,(
    ! [A_7] : k3_subset_1(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_90])).

tff(c_264,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(u1_struct_0(A_56),k2_pre_topc(A_56,k3_subset_1(u1_struct_0(A_56),B_57))) = k1_tops_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_280,plain,(
    ! [A_56] :
      ( k3_subset_1(u1_struct_0(A_56),k2_pre_topc(A_56,k1_xboole_0)) = k1_tops_1(A_56,u1_struct_0(A_56))
      | ~ m1_subset_1(u1_struct_0(A_56),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_264])).

tff(c_328,plain,(
    ! [A_59] :
      ( k3_subset_1(u1_struct_0(A_59),k2_pre_topc(A_59,k1_xboole_0)) = k1_tops_1(A_59,u1_struct_0(A_59))
      | ~ l1_pre_topc(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_280])).

tff(c_340,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_328])).

tff(c_347,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75,c_75,c_37,c_340])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.16/1.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.16/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.16/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.16/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.16/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.16/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.28  
% 2.16/1.30  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.16/1.30  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.16/1.30  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.16/1.30  tff(f_28, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.16/1.30  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.16/1.30  tff(f_38, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.16/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.30  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.16/1.30  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.16/1.30  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.16/1.30  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.16/1.30  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.16/1.30  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.16/1.30  tff(c_30, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.30  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.30  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.16/1.30  tff(c_66, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.30  tff(c_71, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_22, c_66])).
% 2.16/1.30  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_71])).
% 2.16/1.30  tff(c_4, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.16/1.30  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.16/1.30  tff(c_12, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=k2_subset_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.30  tff(c_35, plain, (![A_6]: (k3_subset_1(A_6, k1_subset_1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 2.16/1.30  tff(c_37, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_35])).
% 2.16/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.16/1.30  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.30  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.30  tff(c_115, plain, (![B_40, A_41]: (v4_pre_topc(B_40, A_41) | ~v1_xboole_0(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.30  tff(c_118, plain, (![B_40]: (v4_pre_topc(B_40, '#skF_1') | ~v1_xboole_0(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_115])).
% 2.16/1.30  tff(c_134, plain, (![B_43]: (v4_pre_topc(B_43, '#skF_1') | ~v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_118])).
% 2.16/1.30  tff(c_138, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_134])).
% 2.16/1.30  tff(c_145, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_138])).
% 2.16/1.30  tff(c_148, plain, (![A_44, B_45]: (k2_pre_topc(A_44, B_45)=B_45 | ~v4_pre_topc(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.16/1.30  tff(c_164, plain, (![A_46]: (k2_pre_topc(A_46, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_14, c_148])).
% 2.16/1.30  tff(c_167, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_145, c_164])).
% 2.16/1.30  tff(c_173, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.16/1.30  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.30  tff(c_36, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.16/1.30  tff(c_88, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.16/1.30  tff(c_90, plain, (![A_7]: (k3_subset_1(A_7, k3_subset_1(A_7, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_88])).
% 2.16/1.30  tff(c_94, plain, (![A_7]: (k3_subset_1(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_90])).
% 2.16/1.30  tff(c_264, plain, (![A_56, B_57]: (k3_subset_1(u1_struct_0(A_56), k2_pre_topc(A_56, k3_subset_1(u1_struct_0(A_56), B_57)))=k1_tops_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.16/1.30  tff(c_280, plain, (![A_56]: (k3_subset_1(u1_struct_0(A_56), k2_pre_topc(A_56, k1_xboole_0))=k1_tops_1(A_56, u1_struct_0(A_56)) | ~m1_subset_1(u1_struct_0(A_56), k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(superposition, [status(thm), theory('equality')], [c_94, c_264])).
% 2.16/1.30  tff(c_328, plain, (![A_59]: (k3_subset_1(u1_struct_0(A_59), k2_pre_topc(A_59, k1_xboole_0))=k1_tops_1(A_59, u1_struct_0(A_59)) | ~l1_pre_topc(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_280])).
% 2.16/1.30  tff(c_340, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_173, c_328])).
% 2.16/1.30  tff(c_347, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75, c_75, c_37, c_340])).
% 2.16/1.30  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_347])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 64
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 2
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 5
% 2.16/1.30  #Demod        : 51
% 2.16/1.30  #Tautology    : 28
% 2.16/1.30  #SimpNegUnit  : 4
% 2.16/1.30  #BackRed      : 0
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.43/1.30  Preprocessing        : 0.30
% 2.43/1.30  Parsing              : 0.16
% 2.43/1.30  CNF conversion       : 0.02
% 2.43/1.30  Main loop            : 0.22
% 2.43/1.30  Inferencing          : 0.08
% 2.43/1.30  Reduction            : 0.07
% 2.43/1.30  Demodulation         : 0.05
% 2.43/1.30  BG Simplification    : 0.01
% 2.43/1.30  Subsumption          : 0.03
% 2.43/1.30  Abstraction          : 0.01
% 2.43/1.30  MUC search           : 0.00
% 2.43/1.30  Cooper               : 0.00
% 2.43/1.30  Total                : 0.55
% 2.43/1.30  Index Insertion      : 0.00
% 2.43/1.30  Index Deletion       : 0.00
% 2.43/1.30  Index Matching       : 0.00
% 2.43/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
