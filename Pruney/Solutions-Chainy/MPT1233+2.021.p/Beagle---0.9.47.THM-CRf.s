%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:32 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 146 expanded)
%              Number of leaves         :   41 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 226 expanded)
%              Number of equality atoms :   39 (  79 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_36,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_38,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_116,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_125,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_136,plain,(
    ! [A_50] : k4_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_8])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    k1_tops_1('#skF_1',k2_struct_0('#skF_1')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_subset_1(A_11)) = k2_subset_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_subset_1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_46,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_249,plain,(
    ! [B_67,A_68] :
      ( v4_pre_topc(B_67,A_68)
      | ~ v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_260,plain,(
    ! [A_68] :
      ( v4_pre_topc(k1_xboole_0,A_68)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_20,c_249])).

tff(c_267,plain,(
    ! [A_69] :
      ( v4_pre_topc(k1_xboole_0,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_260])).

tff(c_32,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_100,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_159,plain,(
    ! [A_59,B_60] :
      ( k2_pre_topc(A_59,B_60) = B_60
      | ~ v4_pre_topc(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_166,plain,(
    ! [B_60] :
      ( k2_pre_topc('#skF_1',B_60) = B_60
      | ~ v4_pre_topc(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_159])).

tff(c_220,plain,(
    ! [B_65] :
      ( k2_pre_topc('#skF_1',B_65) = B_65
      | ~ v4_pre_topc(B_65,'#skF_1')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_230,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_220])).

tff(c_231,plain,(
    ~ v4_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_270,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_267,c_231])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_270])).

tff(c_278,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_151,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_155,plain,(
    ! [A_12] : k3_subset_1(A_12,k3_subset_1(A_12,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_151])).

tff(c_158,plain,(
    ! [A_12] : k3_subset_1(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_155])).

tff(c_567,plain,(
    ! [A_97,B_98] :
      ( k3_subset_1(u1_struct_0(A_97),k2_pre_topc(A_97,k3_subset_1(u1_struct_0(A_97),B_98))) = k1_tops_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_596,plain,(
    ! [B_98] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_98))) = k1_tops_1('#skF_1',B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_567])).

tff(c_642,plain,(
    ! [B_100] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_100))) = k1_tops_1('#skF_1',B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_100,c_100,c_596])).

tff(c_668,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k1_xboole_0)) = k1_tops_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_642])).

tff(c_675,plain,
    ( k1_tops_1('#skF_1',k2_struct_0('#skF_1')) = k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_278,c_668])).

tff(c_676,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_675])).

tff(c_681,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_676])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.93  
% 3.58/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.93  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1
% 3.58/1.93  
% 3.58/1.93  %Foreground sorts:
% 3.58/1.93  
% 3.58/1.93  
% 3.58/1.93  %Background operators:
% 3.58/1.93  
% 3.58/1.93  
% 3.58/1.93  %Foreground operators:
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.58/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.58/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.58/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.58/1.93  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.58/1.93  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.58/1.93  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.93  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.58/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.58/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.58/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.58/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.58/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.94  
% 3.58/1.96  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.58/1.96  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.58/1.96  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.58/1.96  tff(f_32, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.58/1.96  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.58/1.96  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.58/1.96  tff(f_36, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.58/1.96  tff(f_38, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.58/1.96  tff(f_44, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.58/1.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.58/1.96  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.58/1.96  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.58/1.96  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.58/1.96  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.58/1.96  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.58/1.96  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.58/1.96  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 3.58/1.96  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.96  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.58/1.96  tff(c_116, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.58/1.96  tff(c_125, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_116])).
% 3.58/1.96  tff(c_136, plain, (![A_50]: (k4_xboole_0(A_50, k1_xboole_0)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_125])).
% 3.58/1.96  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.58/1.96  tff(c_142, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_136, c_8])).
% 3.58/1.96  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.58/1.96  tff(c_40, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.58/1.96  tff(c_12, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.58/1.96  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.58/1.96  tff(c_18, plain, (![A_11]: (k3_subset_1(A_11, k1_subset_1(A_11))=k2_subset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.58/1.96  tff(c_45, plain, (![A_11]: (k3_subset_1(A_11, k1_subset_1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 3.58/1.96  tff(c_46, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_45])).
% 3.58/1.96  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.58/1.96  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.58/1.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.58/1.96  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.58/1.96  tff(c_249, plain, (![B_67, A_68]: (v4_pre_topc(B_67, A_68) | ~v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.96  tff(c_260, plain, (![A_68]: (v4_pre_topc(k1_xboole_0, A_68) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68))), inference(resolution, [status(thm)], [c_20, c_249])).
% 3.58/1.96  tff(c_267, plain, (![A_69]: (v4_pre_topc(k1_xboole_0, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_260])).
% 3.58/1.96  tff(c_32, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.58/1.96  tff(c_91, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.58/1.96  tff(c_96, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_32, c_91])).
% 3.58/1.96  tff(c_100, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_96])).
% 3.58/1.96  tff(c_159, plain, (![A_59, B_60]: (k2_pre_topc(A_59, B_60)=B_60 | ~v4_pre_topc(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.58/1.96  tff(c_166, plain, (![B_60]: (k2_pre_topc('#skF_1', B_60)=B_60 | ~v4_pre_topc(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_159])).
% 3.58/1.96  tff(c_220, plain, (![B_65]: (k2_pre_topc('#skF_1', B_65)=B_65 | ~v4_pre_topc(B_65, '#skF_1') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_166])).
% 3.58/1.96  tff(c_230, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_20, c_220])).
% 3.58/1.96  tff(c_231, plain, (~v4_pre_topc(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_230])).
% 3.58/1.96  tff(c_270, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_267, c_231])).
% 3.58/1.96  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_270])).
% 3.58/1.96  tff(c_278, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_230])).
% 3.58/1.96  tff(c_151, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.58/1.96  tff(c_155, plain, (![A_12]: (k3_subset_1(A_12, k3_subset_1(A_12, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_151])).
% 3.58/1.96  tff(c_158, plain, (![A_12]: (k3_subset_1(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_155])).
% 3.58/1.96  tff(c_567, plain, (![A_97, B_98]: (k3_subset_1(u1_struct_0(A_97), k2_pre_topc(A_97, k3_subset_1(u1_struct_0(A_97), B_98)))=k1_tops_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.58/1.96  tff(c_596, plain, (![B_98]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_98)))=k1_tops_1('#skF_1', B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_567])).
% 3.58/1.96  tff(c_642, plain, (![B_100]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_100)))=k1_tops_1('#skF_1', B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_100, c_100, c_596])).
% 3.58/1.96  tff(c_668, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k1_xboole_0))=k1_tops_1('#skF_1', k2_struct_0('#skF_1')) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_642])).
% 3.58/1.96  tff(c_675, plain, (k1_tops_1('#skF_1', k2_struct_0('#skF_1'))=k2_struct_0('#skF_1') | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_278, c_668])).
% 3.58/1.96  tff(c_676, plain, (~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_675])).
% 3.58/1.96  tff(c_681, plain, (~r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_676])).
% 3.58/1.96  tff(c_685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_681])).
% 3.58/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.96  
% 3.58/1.96  Inference rules
% 3.58/1.96  ----------------------
% 3.58/1.96  #Ref     : 0
% 3.58/1.96  #Sup     : 128
% 3.58/1.96  #Fact    : 0
% 3.58/1.96  #Define  : 0
% 3.58/1.96  #Split   : 3
% 3.58/1.96  #Chain   : 0
% 3.58/1.96  #Close   : 0
% 3.58/1.96  
% 3.58/1.96  Ordering : KBO
% 3.58/1.96  
% 3.58/1.96  Simplification rules
% 3.58/1.96  ----------------------
% 3.58/1.96  #Subsume      : 18
% 3.58/1.96  #Demod        : 81
% 3.58/1.96  #Tautology    : 48
% 3.58/1.96  #SimpNegUnit  : 9
% 3.58/1.96  #BackRed      : 0
% 3.58/1.96  
% 3.58/1.96  #Partial instantiations: 0
% 3.58/1.96  #Strategies tried      : 1
% 3.58/1.96  
% 3.58/1.96  Timing (in seconds)
% 3.58/1.96  ----------------------
% 3.58/1.97  Preprocessing        : 0.51
% 3.58/1.97  Parsing              : 0.26
% 3.58/1.97  CNF conversion       : 0.03
% 3.58/1.97  Main loop            : 0.53
% 3.58/1.97  Inferencing          : 0.21
% 3.58/1.97  Reduction            : 0.17
% 3.58/1.97  Demodulation         : 0.12
% 3.58/1.97  BG Simplification    : 0.03
% 3.58/1.97  Subsumption          : 0.08
% 3.58/1.97  Abstraction          : 0.03
% 3.58/1.97  MUC search           : 0.00
% 3.58/1.97  Cooper               : 0.00
% 3.58/1.97  Total                : 1.10
% 3.58/1.97  Index Insertion      : 0.00
% 3.58/1.97  Index Deletion       : 0.00
% 3.58/1.97  Index Matching       : 0.00
% 3.58/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
