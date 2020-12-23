%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:22 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 196 expanded)
%              Number of leaves         :   33 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 300 expanded)
%              Number of equality atoms :   25 (  98 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

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

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_39,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_201,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k3_subset_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_232,plain,(
    ! [B_54,A_55] :
      ( k4_xboole_0(B_54,A_55) = k3_subset_1(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_201])).

tff(c_235,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = k3_subset_1(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_232])).

tff(c_244,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_28,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_16] :
      ( v1_xboole_0(k1_struct_0(A_16))
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(B_28)
      | B_28 = A_29
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_81,plain,(
    ! [A_31] :
      ( k1_struct_0(A_31) = k1_xboole_0
      | ~ l1_struct_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_86,plain,(
    ! [A_32] :
      ( k1_struct_0(A_32) = k1_xboole_0
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_90,plain,(
    k1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_86])).

tff(c_127,plain,(
    ! [A_41] :
      ( k3_subset_1(u1_struct_0(A_41),k1_struct_0(A_41)) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_136,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_127])).

tff(c_165,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_165])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_177])).

tff(c_182,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k1_xboole_0) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_250,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_182])).

tff(c_338,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k2_pre_topc(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_349,plain,(
    ! [B_65] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_65),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_338])).

tff(c_355,plain,(
    ! [B_66] :
      ( m1_subset_1(k2_pre_topc('#skF_1',B_66),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_250,c_349])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_367,plain,(
    ! [B_67] :
      ( r1_tarski(k2_pre_topc('#skF_1',B_67),k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_355,c_22])).

tff(c_36,plain,(
    k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_259,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(B_57,k2_pre_topc(A_58,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_284,plain,(
    ! [A_59] :
      ( r1_tarski(u1_struct_0(A_59),k2_pre_topc(A_59,u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_39,c_259])).

tff(c_292,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_284])).

tff(c_299,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_250,c_292])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_306,plain,
    ( k2_pre_topc('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_299,c_4])).

tff(c_310,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k2_struct_0('#skF_1')),k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_306])).

tff(c_370,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_367,c_310])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  
% 2.28/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.33  %$ r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1
% 2.28/1.33  
% 2.28/1.33  %Foreground sorts:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Background operators:
% 2.28/1.33  
% 2.28/1.33  
% 2.28/1.33  %Foreground operators:
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.28/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.33  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 2.28/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.28/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.28/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.33  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.28/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.33  
% 2.28/1.35  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.28/1.35  tff(f_52, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.28/1.35  tff(f_86, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tops_1)).
% 2.28/1.35  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.28/1.35  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.28/1.35  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.35  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.28/1.35  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.28/1.35  tff(f_70, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_struct_0)).
% 2.28/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.35  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.28/1.35  tff(f_74, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_pre_topc)).
% 2.28/1.35  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.28/1.35  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 2.28/1.35  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.35  tff(c_16, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.35  tff(c_20, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.35  tff(c_39, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.28/1.35  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.28/1.35  tff(c_12, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.28/1.35  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.35  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.35  tff(c_201, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k3_subset_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.35  tff(c_232, plain, (![B_54, A_55]: (k4_xboole_0(B_54, A_55)=k3_subset_1(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_24, c_201])).
% 2.28/1.35  tff(c_235, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=k3_subset_1(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_232])).
% 2.28/1.35  tff(c_244, plain, (![A_56]: (k3_subset_1(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_235])).
% 2.28/1.35  tff(c_28, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.35  tff(c_30, plain, (![A_16]: (v1_xboole_0(k1_struct_0(A_16)) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.28/1.35  tff(c_64, plain, (![B_28, A_29]: (~v1_xboole_0(B_28) | B_28=A_29 | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.35  tff(c_71, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_2, c_64])).
% 2.28/1.35  tff(c_81, plain, (![A_31]: (k1_struct_0(A_31)=k1_xboole_0 | ~l1_struct_0(A_31))), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.28/1.35  tff(c_86, plain, (![A_32]: (k1_struct_0(A_32)=k1_xboole_0 | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.28/1.35  tff(c_90, plain, (k1_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_86])).
% 2.28/1.35  tff(c_127, plain, (![A_41]: (k3_subset_1(u1_struct_0(A_41), k1_struct_0(A_41))=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.35  tff(c_136, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_127])).
% 2.28/1.35  tff(c_165, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_136])).
% 2.28/1.35  tff(c_177, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_165])).
% 2.28/1.35  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_177])).
% 2.28/1.35  tff(c_182, plain, (k3_subset_1(u1_struct_0('#skF_1'), k1_xboole_0)=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_136])).
% 2.28/1.35  tff(c_250, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_244, c_182])).
% 2.28/1.35  tff(c_338, plain, (![A_64, B_65]: (m1_subset_1(k2_pre_topc(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.35  tff(c_349, plain, (![B_65]: (m1_subset_1(k2_pre_topc('#skF_1', B_65), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_338])).
% 2.28/1.35  tff(c_355, plain, (![B_66]: (m1_subset_1(k2_pre_topc('#skF_1', B_66), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_250, c_349])).
% 2.28/1.35  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.35  tff(c_367, plain, (![B_67]: (r1_tarski(k2_pre_topc('#skF_1', B_67), k2_struct_0('#skF_1')) | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_355, c_22])).
% 2.28/1.35  tff(c_36, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.28/1.35  tff(c_259, plain, (![B_57, A_58]: (r1_tarski(B_57, k2_pre_topc(A_58, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.28/1.35  tff(c_284, plain, (![A_59]: (r1_tarski(u1_struct_0(A_59), k2_pre_topc(A_59, u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_39, c_259])).
% 2.28/1.35  tff(c_292, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_250, c_284])).
% 2.28/1.35  tff(c_299, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_250, c_292])).
% 2.28/1.35  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.35  tff(c_306, plain, (k2_pre_topc('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_299, c_4])).
% 2.28/1.35  tff(c_310, plain, (~r1_tarski(k2_pre_topc('#skF_1', k2_struct_0('#skF_1')), k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_306])).
% 2.28/1.35  tff(c_370, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_367, c_310])).
% 2.28/1.35  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_370])).
% 2.28/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  Inference rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Ref     : 0
% 2.28/1.35  #Sup     : 77
% 2.28/1.35  #Fact    : 0
% 2.28/1.35  #Define  : 0
% 2.28/1.35  #Split   : 1
% 2.28/1.35  #Chain   : 0
% 2.28/1.35  #Close   : 0
% 2.28/1.35  
% 2.28/1.35  Ordering : KBO
% 2.28/1.35  
% 2.28/1.35  Simplification rules
% 2.28/1.35  ----------------------
% 2.28/1.35  #Subsume      : 4
% 2.28/1.35  #Demod        : 30
% 2.28/1.35  #Tautology    : 35
% 2.28/1.35  #SimpNegUnit  : 1
% 2.28/1.35  #BackRed      : 1
% 2.28/1.35  
% 2.28/1.35  #Partial instantiations: 0
% 2.28/1.35  #Strategies tried      : 1
% 2.28/1.35  
% 2.28/1.35  Timing (in seconds)
% 2.28/1.35  ----------------------
% 2.28/1.35  Preprocessing        : 0.31
% 2.28/1.35  Parsing              : 0.18
% 2.28/1.35  CNF conversion       : 0.02
% 2.28/1.35  Main loop            : 0.22
% 2.28/1.35  Inferencing          : 0.08
% 2.28/1.35  Reduction            : 0.06
% 2.28/1.35  Demodulation         : 0.05
% 2.28/1.35  BG Simplification    : 0.01
% 2.28/1.35  Subsumption          : 0.04
% 2.28/1.35  Abstraction          : 0.01
% 2.28/1.35  MUC search           : 0.00
% 2.28/1.35  Cooper               : 0.00
% 2.28/1.35  Total                : 0.56
% 2.28/1.35  Index Insertion      : 0.00
% 2.28/1.35  Index Deletion       : 0.00
% 2.28/1.35  Index Matching       : 0.00
% 2.28/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
