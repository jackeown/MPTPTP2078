%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 138 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 226 expanded)
%              Number of equality atoms :   31 (  71 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_89,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    k1_tops_1('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = k2_subset_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_subset_1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_44,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_288,plain,(
    ! [B_78,A_79] :
      ( v4_pre_topc(B_78,A_79)
      | ~ v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_307,plain,(
    ! [A_79] :
      ( v4_pre_topc(k1_xboole_0,A_79)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_18,c_288])).

tff(c_316,plain,(
    ! [A_80] :
      ( v4_pre_topc(k1_xboole_0,A_80)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_307])).

tff(c_30,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_77,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_30,c_72])).

tff(c_81,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_178,plain,(
    ! [A_61,B_62] :
      ( k2_pre_topc(A_61,B_62) = B_62
      | ~ v4_pre_topc(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_185,plain,(
    ! [B_62] :
      ( k2_pre_topc('#skF_2',B_62) = B_62
      | ~ v4_pre_topc(B_62,'#skF_2')
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_178])).

tff(c_230,plain,(
    ! [B_70] :
      ( k2_pre_topc('#skF_2',B_70) = B_70
      | ~ v4_pre_topc(B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_185])).

tff(c_245,plain,
    ( k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_230])).

tff(c_246,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_319,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_316,c_246])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_319])).

tff(c_327,plain,(
    k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_126,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_11] : k3_subset_1(A_11,k3_subset_1(A_11,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_126])).

tff(c_133,plain,(
    ! [A_11] : k3_subset_1(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_130])).

tff(c_674,plain,(
    ! [A_119,B_120] :
      ( k3_subset_1(u1_struct_0(A_119),k2_pre_topc(A_119,k3_subset_1(u1_struct_0(A_119),B_120))) = k1_tops_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_703,plain,(
    ! [B_120] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_120))) = k1_tops_1('#skF_2',B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_674])).

tff(c_749,plain,(
    ! [B_122] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_122))) = k1_tops_1('#skF_2',B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_81,c_81,c_703])).

tff(c_775,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k1_xboole_0)) = k1_tops_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_749])).

tff(c_782,plain,
    ( k1_tops_1('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_327,c_775])).

tff(c_783,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_782])).

tff(c_788,plain,(
    ~ r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_783])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.45  
% 3.11/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.45  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.11/1.45  
% 3.11/1.45  %Foreground sorts:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Background operators:
% 3.11/1.45  
% 3.11/1.45  
% 3.11/1.45  %Foreground operators:
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.11/1.45  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.11/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.11/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.45  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.11/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.11/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.11/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.45  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.11/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.45  
% 3.11/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.11/1.47  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.11/1.47  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.11/1.47  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.11/1.47  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.11/1.47  tff(f_43, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.11/1.47  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.11/1.47  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.11/1.47  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.11/1.47  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.11/1.47  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.11/1.47  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.11/1.47  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.11/1.47  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.11/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.47  tff(c_98, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.47  tff(c_103, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_98])).
% 3.11/1.47  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.11/1.47  tff(c_38, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.11/1.47  tff(c_10, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.47  tff(c_12, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.47  tff(c_16, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=k2_subset_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.47  tff(c_43, plain, (![A_10]: (k3_subset_1(A_10, k1_subset_1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 3.11/1.47  tff(c_44, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_43])).
% 3.11/1.47  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.11/1.47  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.11/1.47  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.47  tff(c_18, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.47  tff(c_288, plain, (![B_78, A_79]: (v4_pre_topc(B_78, A_79) | ~v1_xboole_0(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.11/1.47  tff(c_307, plain, (![A_79]: (v4_pre_topc(k1_xboole_0, A_79) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(resolution, [status(thm)], [c_18, c_288])).
% 3.11/1.47  tff(c_316, plain, (![A_80]: (v4_pre_topc(k1_xboole_0, A_80) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_307])).
% 3.11/1.47  tff(c_30, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.11/1.47  tff(c_72, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.47  tff(c_77, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_30, c_72])).
% 3.11/1.47  tff(c_81, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_77])).
% 3.11/1.47  tff(c_178, plain, (![A_61, B_62]: (k2_pre_topc(A_61, B_62)=B_62 | ~v4_pre_topc(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.47  tff(c_185, plain, (![B_62]: (k2_pre_topc('#skF_2', B_62)=B_62 | ~v4_pre_topc(B_62, '#skF_2') | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_178])).
% 3.11/1.47  tff(c_230, plain, (![B_70]: (k2_pre_topc('#skF_2', B_70)=B_70 | ~v4_pre_topc(B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_185])).
% 3.11/1.47  tff(c_245, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_18, c_230])).
% 3.11/1.47  tff(c_246, plain, (~v4_pre_topc(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_245])).
% 3.11/1.47  tff(c_319, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_316, c_246])).
% 3.11/1.47  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_319])).
% 3.11/1.47  tff(c_327, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_245])).
% 3.11/1.47  tff(c_126, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.47  tff(c_130, plain, (![A_11]: (k3_subset_1(A_11, k3_subset_1(A_11, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_126])).
% 3.11/1.47  tff(c_133, plain, (![A_11]: (k3_subset_1(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_130])).
% 3.11/1.47  tff(c_674, plain, (![A_119, B_120]: (k3_subset_1(u1_struct_0(A_119), k2_pre_topc(A_119, k3_subset_1(u1_struct_0(A_119), B_120)))=k1_tops_1(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.11/1.47  tff(c_703, plain, (![B_120]: (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_120)))=k1_tops_1('#skF_2', B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_674])).
% 3.11/1.47  tff(c_749, plain, (![B_122]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_122)))=k1_tops_1('#skF_2', B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_81, c_81, c_703])).
% 3.11/1.47  tff(c_775, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k1_xboole_0))=k1_tops_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_133, c_749])).
% 3.11/1.47  tff(c_782, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2') | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_327, c_775])).
% 3.11/1.47  tff(c_783, plain, (~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_782])).
% 3.11/1.47  tff(c_788, plain, (~r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_783])).
% 3.11/1.47  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_788])).
% 3.11/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  
% 3.11/1.47  Inference rules
% 3.11/1.47  ----------------------
% 3.11/1.47  #Ref     : 0
% 3.11/1.47  #Sup     : 153
% 3.11/1.47  #Fact    : 0
% 3.11/1.47  #Define  : 0
% 3.11/1.47  #Split   : 2
% 3.11/1.47  #Chain   : 0
% 3.11/1.47  #Close   : 0
% 3.11/1.47  
% 3.11/1.47  Ordering : KBO
% 3.11/1.47  
% 3.11/1.47  Simplification rules
% 3.11/1.47  ----------------------
% 3.11/1.47  #Subsume      : 17
% 3.11/1.47  #Demod        : 66
% 3.11/1.47  #Tautology    : 42
% 3.11/1.47  #SimpNegUnit  : 5
% 3.11/1.47  #BackRed      : 0
% 3.11/1.47  
% 3.11/1.47  #Partial instantiations: 0
% 3.11/1.47  #Strategies tried      : 1
% 3.11/1.47  
% 3.11/1.47  Timing (in seconds)
% 3.11/1.47  ----------------------
% 3.11/1.47  Preprocessing        : 0.34
% 3.11/1.47  Parsing              : 0.18
% 3.11/1.47  CNF conversion       : 0.02
% 3.11/1.47  Main loop            : 0.38
% 3.11/1.47  Inferencing          : 0.15
% 3.11/1.47  Reduction            : 0.11
% 3.11/1.48  Demodulation         : 0.08
% 3.11/1.48  BG Simplification    : 0.02
% 3.11/1.48  Subsumption          : 0.06
% 3.11/1.48  Abstraction          : 0.02
% 3.11/1.48  MUC search           : 0.00
% 3.11/1.48  Cooper               : 0.00
% 3.11/1.48  Total                : 0.75
% 3.11/1.48  Index Insertion      : 0.00
% 3.11/1.48  Index Deletion       : 0.00
% 3.11/1.48  Index Matching       : 0.00
% 3.11/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
