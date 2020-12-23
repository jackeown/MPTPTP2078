%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:31 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 192 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 265 expanded)
%              Number of equality atoms :   39 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_34,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_95,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k4_subset_1(u1_struct_0(A),B,k3_subset_1(u1_struct_0(A),B)) = k2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_47,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_45])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_201,plain,(
    ! [B_62,A_63] :
      ( v4_pre_topc(B_62,A_63)
      | ~ v1_xboole_0(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_209,plain,(
    ! [A_63] :
      ( v4_pre_topc(k1_xboole_0,A_63)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_214,plain,(
    ! [A_64] :
      ( v4_pre_topc(k1_xboole_0,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_128,plain,(
    ! [A_53,B_54] :
      ( k2_pre_topc(A_53,B_54) = B_54
      | ~ v4_pre_topc(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_138,plain,(
    ! [A_53] :
      ( k2_pre_topc(A_53,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_20,c_128])).

tff(c_219,plain,(
    ! [A_65] :
      ( k2_pre_topc(A_65,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_214,c_138])).

tff(c_222,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_219])).

tff(c_225,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_222])).

tff(c_120,plain,(
    ! [A_51,B_52] :
      ( k3_subset_1(A_51,k3_subset_1(A_51,B_52)) = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_124,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_120])).

tff(c_127,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_124])).

tff(c_30,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( k4_subset_1(A_8,B_9,k3_subset_1(A_8,B_9)) = k2_subset_1(A_8)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_184,plain,(
    ! [A_59,B_60] :
      ( k4_subset_1(A_59,B_60,k3_subset_1(A_59,B_60)) = A_59
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_188,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,k3_subset_1(A_10,k1_xboole_0)) = A_10 ),
    inference(resolution,[status(thm)],[c_20,c_184])).

tff(c_191,plain,(
    ! [A_10] : k4_subset_1(A_10,k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_188])).

tff(c_307,plain,(
    ! [A_76,B_77] :
      ( k4_subset_1(u1_struct_0(A_76),B_77,k3_subset_1(u1_struct_0(A_76),B_77)) = k2_struct_0(A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_332,plain,(
    ! [A_76] :
      ( k4_subset_1(u1_struct_0(A_76),k1_xboole_0,u1_struct_0(A_76)) = k2_struct_0(A_76)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_struct_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_307])).

tff(c_338,plain,(
    ! [A_78] :
      ( u1_struct_0(A_78) = k2_struct_0(A_78)
      | ~ l1_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_191,c_332])).

tff(c_343,plain,(
    ! [A_79] :
      ( u1_struct_0(A_79) = k2_struct_0(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_30,c_338])).

tff(c_347,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_343])).

tff(c_411,plain,(
    ! [A_81,B_82] :
      ( k3_subset_1(u1_struct_0(A_81),k2_pre_topc(A_81,k3_subset_1(u1_struct_0(A_81),B_82))) = k1_tops_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_435,plain,(
    ! [B_82] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_82))) = k1_tops_1('#skF_1',B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_411])).

tff(c_601,plain,(
    ! [B_93] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_93))) = k1_tops_1('#skF_1',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_347,c_347,c_435])).

tff(c_630,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_601])).

tff(c_637,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_225,c_630])).

tff(c_638,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_637])).

tff(c_643,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_638])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_subset_1 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 2.60/1.40  
% 2.60/1.40  %Foreground sorts:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Background operators:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Foreground operators:
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.60/1.40  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.60/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.60/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.40  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.60/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.60/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.60/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.60/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.40  
% 2.93/1.42  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.42  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.93/1.42  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 2.93/1.42  tff(f_34, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.93/1.42  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.93/1.42  tff(f_42, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.93/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.93/1.42  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.93/1.42  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.93/1.42  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.93/1.42  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.93/1.42  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.93/1.42  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.93/1.42  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k4_subset_1(u1_struct_0(A), B, k3_subset_1(u1_struct_0(A), B)) = k2_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_pre_topc)).
% 2.93/1.42  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 2.93/1.42  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.42  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.93/1.42  tff(c_40, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.42  tff(c_10, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.93/1.42  tff(c_12, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.93/1.42  tff(c_16, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.93/1.42  tff(c_45, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.93/1.42  tff(c_47, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_45])).
% 2.93/1.42  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.42  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.93/1.42  tff(c_20, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.93/1.42  tff(c_201, plain, (![B_62, A_63]: (v4_pre_topc(B_62, A_63) | ~v1_xboole_0(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.93/1.42  tff(c_209, plain, (![A_63]: (v4_pre_topc(k1_xboole_0, A_63) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(resolution, [status(thm)], [c_20, c_201])).
% 2.93/1.42  tff(c_214, plain, (![A_64]: (v4_pre_topc(k1_xboole_0, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_209])).
% 2.93/1.42  tff(c_128, plain, (![A_53, B_54]: (k2_pre_topc(A_53, B_54)=B_54 | ~v4_pre_topc(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.93/1.42  tff(c_138, plain, (![A_53]: (k2_pre_topc(A_53, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_20, c_128])).
% 2.93/1.42  tff(c_219, plain, (![A_65]: (k2_pre_topc(A_65, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(resolution, [status(thm)], [c_214, c_138])).
% 2.93/1.42  tff(c_222, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_219])).
% 2.93/1.42  tff(c_225, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_222])).
% 2.93/1.42  tff(c_120, plain, (![A_51, B_52]: (k3_subset_1(A_51, k3_subset_1(A_51, B_52))=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.93/1.42  tff(c_124, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_120])).
% 2.93/1.42  tff(c_127, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_124])).
% 2.93/1.42  tff(c_30, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.42  tff(c_18, plain, (![A_8, B_9]: (k4_subset_1(A_8, B_9, k3_subset_1(A_8, B_9))=k2_subset_1(A_8) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.93/1.42  tff(c_184, plain, (![A_59, B_60]: (k4_subset_1(A_59, B_60, k3_subset_1(A_59, B_60))=A_59 | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 2.93/1.42  tff(c_188, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, k3_subset_1(A_10, k1_xboole_0))=A_10)), inference(resolution, [status(thm)], [c_20, c_184])).
% 2.93/1.42  tff(c_191, plain, (![A_10]: (k4_subset_1(A_10, k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_188])).
% 2.93/1.42  tff(c_307, plain, (![A_76, B_77]: (k4_subset_1(u1_struct_0(A_76), B_77, k3_subset_1(u1_struct_0(A_76), B_77))=k2_struct_0(A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.93/1.42  tff(c_332, plain, (![A_76]: (k4_subset_1(u1_struct_0(A_76), k1_xboole_0, u1_struct_0(A_76))=k2_struct_0(A_76) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_struct_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_47, c_307])).
% 2.93/1.42  tff(c_338, plain, (![A_78]: (u1_struct_0(A_78)=k2_struct_0(A_78) | ~l1_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_191, c_332])).
% 2.93/1.42  tff(c_343, plain, (![A_79]: (u1_struct_0(A_79)=k2_struct_0(A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_30, c_338])).
% 2.93/1.42  tff(c_347, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_343])).
% 2.93/1.42  tff(c_411, plain, (![A_81, B_82]: (k3_subset_1(u1_struct_0(A_81), k2_pre_topc(A_81, k3_subset_1(u1_struct_0(A_81), B_82)))=k1_tops_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.93/1.42  tff(c_435, plain, (![B_82]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_82)))=k1_tops_1('#skF_1', B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_347, c_411])).
% 2.93/1.42  tff(c_601, plain, (![B_93]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_93)))=k1_tops_1('#skF_1', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_347, c_347, c_435])).
% 2.93/1.42  tff(c_630, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_601])).
% 2.93/1.42  tff(c_637, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_225, c_630])).
% 2.93/1.42  tff(c_638, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_637])).
% 2.93/1.42  tff(c_643, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_638])).
% 2.93/1.42  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_643])).
% 2.93/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.42  
% 2.93/1.42  Inference rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Ref     : 0
% 2.93/1.42  #Sup     : 126
% 2.93/1.42  #Fact    : 0
% 2.93/1.42  #Define  : 0
% 2.93/1.42  #Split   : 2
% 2.93/1.42  #Chain   : 0
% 2.93/1.42  #Close   : 0
% 2.93/1.42  
% 2.93/1.42  Ordering : KBO
% 2.93/1.42  
% 2.93/1.42  Simplification rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Subsume      : 13
% 2.93/1.42  #Demod        : 74
% 2.93/1.42  #Tautology    : 52
% 2.93/1.42  #SimpNegUnit  : 4
% 2.93/1.42  #BackRed      : 0
% 2.93/1.42  
% 2.93/1.42  #Partial instantiations: 0
% 2.93/1.42  #Strategies tried      : 1
% 2.93/1.42  
% 2.93/1.42  Timing (in seconds)
% 2.93/1.42  ----------------------
% 2.93/1.42  Preprocessing        : 0.29
% 2.93/1.42  Parsing              : 0.16
% 2.93/1.42  CNF conversion       : 0.02
% 2.93/1.42  Main loop            : 0.31
% 2.93/1.42  Inferencing          : 0.12
% 2.93/1.42  Reduction            : 0.09
% 2.93/1.42  Demodulation         : 0.07
% 2.93/1.42  BG Simplification    : 0.02
% 2.93/1.42  Subsumption          : 0.05
% 2.93/1.42  Abstraction          : 0.01
% 2.93/1.42  MUC search           : 0.00
% 2.93/1.42  Cooper               : 0.00
% 2.93/1.42  Total                : 0.64
% 2.93/1.42  Index Insertion      : 0.00
% 2.93/1.42  Index Deletion       : 0.00
% 2.93/1.42  Index Matching       : 0.00
% 2.93/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
