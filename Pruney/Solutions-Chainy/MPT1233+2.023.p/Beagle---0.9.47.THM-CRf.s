%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:33 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 114 expanded)
%              Number of leaves         :   33 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 176 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_80,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k3_subset_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = k3_subset_1(A_8,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_89,plain,(
    ! [A_8] : k3_subset_1(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_22,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_66,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_62])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_126,plain,(
    ! [B_43,A_44] :
      ( v4_pre_topc(B_43,A_44)
      | ~ v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,(
    ! [B_43] :
      ( v4_pre_topc(B_43,'#skF_1')
      | ~ v1_xboole_0(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_126])).

tff(c_181,plain,(
    ! [B_48] :
      ( v4_pre_topc(B_48,'#skF_1')
      | ~ v1_xboole_0(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_129])).

tff(c_189,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_1')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_181])).

tff(c_193,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_189])).

tff(c_194,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = B_50
      | ~ v4_pre_topc(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_197,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_1',B_50) = B_50
      | ~ v4_pre_topc(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_194])).

tff(c_211,plain,(
    ! [B_51] :
      ( k2_pre_topc('#skF_1',B_51) = B_51
      | ~ v4_pre_topc(B_51,'#skF_1')
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_197])).

tff(c_219,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_211])).

tff(c_223,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_219])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_118,plain,(
    ! [A_41,B_42] :
      ( k3_subset_1(A_41,k3_subset_1(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,(
    ! [A_8] : k3_subset_1(A_8,k3_subset_1(A_8,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_125,plain,(
    ! [A_8] : k3_subset_1(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_122])).

tff(c_312,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(u1_struct_0(A_61),k2_pre_topc(A_61,k3_subset_1(u1_struct_0(A_61),B_62))) = k1_tops_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_328,plain,(
    ! [A_61] :
      ( k3_subset_1(u1_struct_0(A_61),k2_pre_topc(A_61,k1_xboole_0)) = k1_tops_1(A_61,u1_struct_0(A_61))
      | ~ m1_subset_1(u1_struct_0(A_61),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_312])).

tff(c_349,plain,(
    ! [A_63] :
      ( k3_subset_1(u1_struct_0(A_63),k2_pre_topc(A_63,k1_xboole_0)) = k1_tops_1(A_63,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_328])).

tff(c_361,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k1_tops_1('#skF_1',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_349])).

tff(c_368,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_89,c_66,c_66,c_361])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.35  
% 2.20/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.35  %$ v4_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 2.20/1.35  
% 2.20/1.35  %Foreground sorts:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Background operators:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Foreground operators:
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.20/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.20/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.20/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.20/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.20/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.20/1.35  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.20/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.20/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.35  
% 2.44/1.37  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.44/1.37  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.44/1.37  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.44/1.37  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.44/1.37  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.44/1.37  tff(f_63, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.44/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.37  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.44/1.37  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.44/1.37  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.44/1.37  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.44/1.37  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.44/1.37  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.44/1.37  tff(c_30, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.44/1.37  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.44/1.37  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.44/1.37  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.37  tff(c_80, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k3_subset_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.44/1.37  tff(c_86, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=k3_subset_1(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.44/1.37  tff(c_89, plain, (![A_8]: (k3_subset_1(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_86])).
% 2.44/1.37  tff(c_22, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.44/1.37  tff(c_57, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.37  tff(c_62, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_22, c_57])).
% 2.44/1.37  tff(c_66, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_62])).
% 2.44/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.44/1.37  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.44/1.37  tff(c_126, plain, (![B_43, A_44]: (v4_pre_topc(B_43, A_44) | ~v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.37  tff(c_129, plain, (![B_43]: (v4_pre_topc(B_43, '#skF_1') | ~v1_xboole_0(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_126])).
% 2.44/1.37  tff(c_181, plain, (![B_48]: (v4_pre_topc(B_48, '#skF_1') | ~v1_xboole_0(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_129])).
% 2.44/1.37  tff(c_189, plain, (v4_pre_topc(k1_xboole_0, '#skF_1') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_181])).
% 2.44/1.37  tff(c_193, plain, (v4_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_189])).
% 2.44/1.37  tff(c_194, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=B_50 | ~v4_pre_topc(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.44/1.37  tff(c_197, plain, (![B_50]: (k2_pre_topc('#skF_1', B_50)=B_50 | ~v4_pre_topc(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_194])).
% 2.44/1.37  tff(c_211, plain, (![B_51]: (k2_pre_topc('#skF_1', B_51)=B_51 | ~v4_pre_topc(B_51, '#skF_1') | ~m1_subset_1(B_51, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_197])).
% 2.44/1.37  tff(c_219, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_14, c_211])).
% 2.44/1.37  tff(c_223, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_219])).
% 2.44/1.37  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.44/1.37  tff(c_10, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.37  tff(c_35, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 2.44/1.37  tff(c_118, plain, (![A_41, B_42]: (k3_subset_1(A_41, k3_subset_1(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.37  tff(c_122, plain, (![A_8]: (k3_subset_1(A_8, k3_subset_1(A_8, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_118])).
% 2.44/1.37  tff(c_125, plain, (![A_8]: (k3_subset_1(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_122])).
% 2.44/1.37  tff(c_312, plain, (![A_61, B_62]: (k3_subset_1(u1_struct_0(A_61), k2_pre_topc(A_61, k3_subset_1(u1_struct_0(A_61), B_62)))=k1_tops_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.44/1.37  tff(c_328, plain, (![A_61]: (k3_subset_1(u1_struct_0(A_61), k2_pre_topc(A_61, k1_xboole_0))=k1_tops_1(A_61, u1_struct_0(A_61)) | ~m1_subset_1(u1_struct_0(A_61), k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(superposition, [status(thm), theory('equality')], [c_125, c_312])).
% 2.44/1.37  tff(c_349, plain, (![A_63]: (k3_subset_1(u1_struct_0(A_63), k2_pre_topc(A_63, k1_xboole_0))=k1_tops_1(A_63, u1_struct_0(A_63)) | ~l1_pre_topc(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_328])).
% 2.44/1.37  tff(c_361, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k1_tops_1('#skF_1', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_223, c_349])).
% 2.44/1.37  tff(c_368, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_89, c_66, c_66, c_361])).
% 2.44/1.37  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_368])).
% 2.44/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  Inference rules
% 2.44/1.37  ----------------------
% 2.44/1.37  #Ref     : 0
% 2.44/1.37  #Sup     : 67
% 2.44/1.37  #Fact    : 0
% 2.44/1.37  #Define  : 0
% 2.44/1.37  #Split   : 2
% 2.44/1.37  #Chain   : 0
% 2.44/1.37  #Close   : 0
% 2.44/1.37  
% 2.44/1.37  Ordering : KBO
% 2.44/1.37  
% 2.44/1.37  Simplification rules
% 2.44/1.37  ----------------------
% 2.44/1.37  #Subsume      : 5
% 2.44/1.37  #Demod        : 48
% 2.44/1.37  #Tautology    : 31
% 2.44/1.37  #SimpNegUnit  : 5
% 2.44/1.37  #BackRed      : 1
% 2.44/1.37  
% 2.44/1.37  #Partial instantiations: 0
% 2.44/1.37  #Strategies tried      : 1
% 2.44/1.37  
% 2.44/1.37  Timing (in seconds)
% 2.44/1.37  ----------------------
% 2.44/1.37  Preprocessing        : 0.28
% 2.44/1.37  Parsing              : 0.15
% 2.44/1.37  CNF conversion       : 0.02
% 2.44/1.37  Main loop            : 0.25
% 2.44/1.37  Inferencing          : 0.10
% 2.44/1.37  Reduction            : 0.08
% 2.44/1.38  Demodulation         : 0.05
% 2.44/1.38  BG Simplification    : 0.02
% 2.44/1.38  Subsumption          : 0.03
% 2.44/1.38  Abstraction          : 0.02
% 2.44/1.38  MUC search           : 0.00
% 2.44/1.38  Cooper               : 0.00
% 2.44/1.38  Total                : 0.57
% 2.44/1.38  Index Insertion      : 0.00
% 2.44/1.38  Index Deletion       : 0.00
% 2.44/1.38  Index Matching       : 0.00
% 2.44/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
