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
% DateTime   : Thu Dec  3 10:20:55 EST 2020

% Result     : Theorem 10.67s
% Output     : CNFRefutation 10.82s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 157 expanded)
%              Number of leaves         :   38 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 257 expanded)
%              Number of equality atoms :   33 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_111,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_98,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | k4_xboole_0(A_62,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_110,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_48])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    ! [A_41] :
      ( l1_struct_0(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_40,c_58])).

tff(c_67,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_52])).

tff(c_689,plain,(
    ! [A_111,B_112,C_113] :
      ( k9_subset_1(A_111,B_112,C_113) = k3_xboole_0(B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_703,plain,(
    ! [B_112] : k9_subset_1(k2_struct_0('#skF_1'),B_112,'#skF_2') = k3_xboole_0(B_112,'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_689])).

tff(c_824,plain,(
    ! [A_121,C_122,B_123] :
      ( k9_subset_1(A_121,C_122,B_123) = k9_subset_1(A_121,B_123,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_832,plain,(
    ! [B_123] : k9_subset_1(k2_struct_0('#skF_1'),B_123,'#skF_2') = k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_123) ),
    inference(resolution,[status(thm)],[c_68,c_824])).

tff(c_839,plain,(
    ! [B_123] : k9_subset_1(k2_struct_0('#skF_1'),'#skF_2',B_123) = k3_xboole_0(B_123,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_832])).

tff(c_50,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1044,plain,(
    ! [A_137,B_138] :
      ( k2_pre_topc(A_137,B_138) = B_138
      | ~ v4_pre_topc(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1054,plain,(
    ! [B_138] :
      ( k2_pre_topc('#skF_1',B_138) = B_138
      | ~ v4_pre_topc(B_138,'#skF_1')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1044])).

tff(c_1119,plain,(
    ! [B_145] :
      ( k2_pre_topc('#skF_1',B_145) = B_145
      | ~ v4_pre_topc(B_145,'#skF_1')
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1054])).

tff(c_1129,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1119])).

tff(c_1138,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1129])).

tff(c_1873,plain,(
    ! [A_173,B_174] :
      ( k9_subset_1(u1_struct_0(A_173),k2_pre_topc(A_173,B_174),k2_pre_topc(A_173,k3_subset_1(u1_struct_0(A_173),B_174))) = k2_tops_1(A_173,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1886,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_1873])).

tff(c_1906,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68,c_67,c_839,c_67,c_67,c_1886])).

tff(c_28,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_89,plain,(
    ! [A_61] : r1_tarski(k1_xboole_0,A_61) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_61] : k2_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k3_xboole_0(A_3,B_4),k3_xboole_0(A_3,C_5)) = k3_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : r1_tarski(k2_xboole_0(k3_xboole_0(A_6,B_7),k3_xboole_0(A_6,C_8)),k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_273,plain,(
    ! [A_75,B_76,C_77] : r1_tarski(k3_xboole_0(A_75,k2_xboole_0(B_76,C_77)),k2_xboole_0(B_76,C_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_294,plain,(
    ! [A_75,A_61] : r1_tarski(k3_xboole_0(A_75,A_61),k2_xboole_0(k1_xboole_0,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_273])).

tff(c_339,plain,(
    ! [A_79,A_80] : r1_tarski(k3_xboole_0(A_79,A_80),A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_294])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_346,plain,(
    ! [A_79,A_80] : k4_xboole_0(k3_xboole_0(A_79,A_80),A_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_339,c_10])).

tff(c_16312,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_346])).

tff(c_16325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_16312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.67/4.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.10  
% 10.82/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.10  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.82/4.10  
% 10.82/4.10  %Foreground sorts:
% 10.82/4.10  
% 10.82/4.10  
% 10.82/4.10  %Background operators:
% 10.82/4.10  
% 10.82/4.10  
% 10.82/4.10  %Foreground operators:
% 10.82/4.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/4.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.82/4.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.82/4.10  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.82/4.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.82/4.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.82/4.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.82/4.10  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.82/4.10  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.82/4.10  tff('#skF_2', type, '#skF_2': $i).
% 10.82/4.10  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.82/4.10  tff('#skF_1', type, '#skF_1': $i).
% 10.82/4.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.82/4.10  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.82/4.10  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.82/4.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/4.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/4.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.82/4.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.82/4.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.82/4.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.82/4.10  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.82/4.10  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.82/4.10  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.82/4.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.82/4.10  
% 10.82/4.12  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 10.82/4.12  tff(f_128, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.82/4.12  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.82/4.12  tff(f_88, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 10.82/4.12  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.82/4.12  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 10.82/4.12  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.82/4.12  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 10.82/4.12  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.82/4.12  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.82/4.12  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.82/4.12  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 10.82/4.12  tff(f_33, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 10.82/4.12  tff(c_98, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | k4_xboole_0(A_62, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.82/4.12  tff(c_48, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.82/4.12  tff(c_110, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_98, c_48])).
% 10.82/4.12  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.82/4.12  tff(c_40, plain, (![A_41]: (l1_struct_0(A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.82/4.12  tff(c_58, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.82/4.12  tff(c_63, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_40, c_58])).
% 10.82/4.12  tff(c_67, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_63])).
% 10.82/4.12  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.82/4.12  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_52])).
% 10.82/4.12  tff(c_689, plain, (![A_111, B_112, C_113]: (k9_subset_1(A_111, B_112, C_113)=k3_xboole_0(B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.82/4.12  tff(c_703, plain, (![B_112]: (k9_subset_1(k2_struct_0('#skF_1'), B_112, '#skF_2')=k3_xboole_0(B_112, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_689])).
% 10.82/4.12  tff(c_824, plain, (![A_121, C_122, B_123]: (k9_subset_1(A_121, C_122, B_123)=k9_subset_1(A_121, B_123, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.82/4.12  tff(c_832, plain, (![B_123]: (k9_subset_1(k2_struct_0('#skF_1'), B_123, '#skF_2')=k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_123))), inference(resolution, [status(thm)], [c_68, c_824])).
% 10.82/4.12  tff(c_839, plain, (![B_123]: (k9_subset_1(k2_struct_0('#skF_1'), '#skF_2', B_123)=k3_xboole_0(B_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_703, c_832])).
% 10.82/4.12  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.82/4.12  tff(c_1044, plain, (![A_137, B_138]: (k2_pre_topc(A_137, B_138)=B_138 | ~v4_pre_topc(B_138, A_137) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.82/4.12  tff(c_1054, plain, (![B_138]: (k2_pre_topc('#skF_1', B_138)=B_138 | ~v4_pre_topc(B_138, '#skF_1') | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1044])).
% 10.82/4.12  tff(c_1119, plain, (![B_145]: (k2_pre_topc('#skF_1', B_145)=B_145 | ~v4_pre_topc(B_145, '#skF_1') | ~m1_subset_1(B_145, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1054])).
% 10.82/4.12  tff(c_1129, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1119])).
% 10.82/4.12  tff(c_1138, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1129])).
% 10.82/4.12  tff(c_1873, plain, (![A_173, B_174]: (k9_subset_1(u1_struct_0(A_173), k2_pre_topc(A_173, B_174), k2_pre_topc(A_173, k3_subset_1(u1_struct_0(A_173), B_174)))=k2_tops_1(A_173, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.82/4.12  tff(c_1886, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1138, c_1873])).
% 10.82/4.12  tff(c_1906, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68, c_67, c_839, c_67, c_67, c_1886])).
% 10.82/4.12  tff(c_28, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.82/4.12  tff(c_76, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.82/4.12  tff(c_89, plain, (![A_61]: (r1_tarski(k1_xboole_0, A_61))), inference(resolution, [status(thm)], [c_28, c_76])).
% 10.82/4.12  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.82/4.12  tff(c_97, plain, (![A_61]: (k2_xboole_0(k1_xboole_0, A_61)=A_61)), inference(resolution, [status(thm)], [c_89, c_2])).
% 10.82/4.12  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k3_xboole_0(A_3, C_5))=k3_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.82/4.12  tff(c_6, plain, (![A_6, B_7, C_8]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_6, B_7), k3_xboole_0(A_6, C_8)), k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.82/4.12  tff(c_273, plain, (![A_75, B_76, C_77]: (r1_tarski(k3_xboole_0(A_75, k2_xboole_0(B_76, C_77)), k2_xboole_0(B_76, C_77)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 10.82/4.12  tff(c_294, plain, (![A_75, A_61]: (r1_tarski(k3_xboole_0(A_75, A_61), k2_xboole_0(k1_xboole_0, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_273])).
% 10.82/4.12  tff(c_339, plain, (![A_79, A_80]: (r1_tarski(k3_xboole_0(A_79, A_80), A_80))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_294])).
% 10.82/4.12  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.82/4.12  tff(c_346, plain, (![A_79, A_80]: (k4_xboole_0(k3_xboole_0(A_79, A_80), A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_339, c_10])).
% 10.82/4.12  tff(c_16312, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1906, c_346])).
% 10.82/4.12  tff(c_16325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_16312])).
% 10.82/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.12  
% 10.82/4.12  Inference rules
% 10.82/4.12  ----------------------
% 10.82/4.12  #Ref     : 0
% 10.82/4.12  #Sup     : 4026
% 10.82/4.12  #Fact    : 0
% 10.82/4.12  #Define  : 0
% 10.82/4.12  #Split   : 6
% 10.82/4.12  #Chain   : 0
% 10.82/4.12  #Close   : 0
% 10.82/4.12  
% 10.82/4.12  Ordering : KBO
% 10.82/4.12  
% 10.82/4.12  Simplification rules
% 10.82/4.12  ----------------------
% 10.82/4.12  #Subsume      : 269
% 10.82/4.12  #Demod        : 5119
% 10.82/4.12  #Tautology    : 2249
% 10.82/4.12  #SimpNegUnit  : 1
% 10.82/4.12  #BackRed      : 63
% 10.82/4.12  
% 10.82/4.12  #Partial instantiations: 0
% 10.82/4.12  #Strategies tried      : 1
% 10.82/4.12  
% 10.82/4.12  Timing (in seconds)
% 10.82/4.12  ----------------------
% 10.82/4.12  Preprocessing        : 0.34
% 10.82/4.12  Parsing              : 0.18
% 10.82/4.12  CNF conversion       : 0.02
% 10.82/4.12  Main loop            : 3.03
% 10.82/4.12  Inferencing          : 0.69
% 10.82/4.12  Reduction            : 1.52
% 10.82/4.12  Demodulation         : 1.28
% 10.82/4.12  BG Simplification    : 0.11
% 10.82/4.12  Subsumption          : 0.56
% 10.82/4.12  Abstraction          : 0.17
% 10.82/4.12  MUC search           : 0.00
% 10.82/4.12  Cooper               : 0.00
% 10.82/4.12  Total                : 3.39
% 10.82/4.12  Index Insertion      : 0.00
% 10.82/4.12  Index Deletion       : 0.00
% 10.82/4.12  Index Matching       : 0.00
% 10.82/4.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
