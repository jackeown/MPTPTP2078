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
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 169 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 399 expanded)
%              Number of equality atoms :   26 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1071,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(k1_tops_1(A_156,B_157),B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1079,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1071])).

tff(c_1084,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1079])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_51,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_57,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_48])).

tff(c_699,plain,(
    ! [B_106,A_107] :
      ( v2_tops_1(B_106,A_107)
      | ~ r1_tarski(B_106,k2_tops_1(A_107,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_703,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_699])).

tff(c_706,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6,c_703])).

tff(c_36,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_831,plain,(
    ! [B_120,A_121] :
      ( v3_tops_1(B_120,A_121)
      | ~ v4_pre_topc(B_120,A_121)
      | ~ v2_tops_1(B_120,A_121)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_842,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_831])).

tff(c_847,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_706,c_36,c_842])).

tff(c_849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_847])).

tff(c_850,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_851,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1132,plain,(
    ! [B_159,A_160] :
      ( v2_tops_1(B_159,A_160)
      | ~ v3_tops_1(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1143,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1132])).

tff(c_1148,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_851,c_1143])).

tff(c_1424,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(B_188,k2_tops_1(A_189,B_188))
      | ~ v2_tops_1(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1432,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1424])).

tff(c_1437,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1148,c_1432])).

tff(c_915,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = k3_subset_1(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_926,plain,(
    ! [B_14,A_13] :
      ( k4_xboole_0(B_14,A_13) = k3_subset_1(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_915])).

tff(c_1097,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1084,c_926])).

tff(c_970,plain,(
    ! [A_144,B_145,C_146] :
      ( k7_subset_1(A_144,B_145,C_146) = k4_xboole_0(B_145,C_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_979,plain,(
    ! [C_146] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_146) = k4_xboole_0('#skF_2',C_146) ),
    inference(resolution,[status(thm)],[c_38,c_970])).

tff(c_1203,plain,(
    ! [A_165,B_166] :
      ( k2_pre_topc(A_165,B_166) = B_166
      | ~ v4_pre_topc(B_166,A_165)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1214,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1203])).

tff(c_1219,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1214])).

tff(c_2015,plain,(
    ! [A_220,B_221] :
      ( k7_subset_1(u1_struct_0(A_220),k2_pre_topc(A_220,B_221),k1_tops_1(A_220,B_221)) = k2_tops_1(A_220,B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2028,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_2015])).

tff(c_2038,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1097,c_979,c_2028])).

tff(c_889,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1(k3_subset_1(A_132,B_133),k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_894,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(k3_subset_1(A_134,B_135),A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_889,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_900,plain,(
    ! [A_134,B_135] :
      ( k3_subset_1(A_134,B_135) = A_134
      | ~ r1_tarski(A_134,k3_subset_1(A_134,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_894,c_2])).

tff(c_2051,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2038,c_900])).

tff(c_2071,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_2038,c_2051])).

tff(c_2072,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_850,c_2071])).

tff(c_2079,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_2072])).

tff(c_2083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_2079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.78  
% 4.37/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.78  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.37/1.78  
% 4.37/1.78  %Foreground sorts:
% 4.37/1.78  
% 4.37/1.78  
% 4.37/1.78  %Background operators:
% 4.37/1.78  
% 4.37/1.78  
% 4.37/1.78  %Foreground operators:
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.78  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.37/1.78  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.37/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.78  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.37/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.78  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.37/1.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.37/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.78  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.37/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.78  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.37/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.37/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.78  
% 4.37/1.79  tff(f_123, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 4.37/1.79  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.37/1.79  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.37/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.37/1.79  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 4.37/1.79  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 4.37/1.79  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 4.37/1.79  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.37/1.79  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.37/1.79  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.37/1.79  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 4.37/1.79  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.37/1.79  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.79  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.79  tff(c_1071, plain, (![A_156, B_157]: (r1_tarski(k1_tops_1(A_156, B_157), B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.37/1.79  tff(c_1079, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1071])).
% 4.37/1.79  tff(c_1084, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1079])).
% 4.37/1.79  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.37/1.79  tff(c_42, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.79  tff(c_51, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.37/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.79  tff(c_48, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.79  tff(c_57, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_51, c_48])).
% 4.37/1.79  tff(c_699, plain, (![B_106, A_107]: (v2_tops_1(B_106, A_107) | ~r1_tarski(B_106, k2_tops_1(A_107, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.79  tff(c_703, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_699])).
% 4.37/1.79  tff(c_706, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6, c_703])).
% 4.37/1.79  tff(c_36, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.79  tff(c_831, plain, (![B_120, A_121]: (v3_tops_1(B_120, A_121) | ~v4_pre_topc(B_120, A_121) | ~v2_tops_1(B_120, A_121) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.37/1.79  tff(c_842, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_831])).
% 4.37/1.79  tff(c_847, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_706, c_36, c_842])).
% 4.37/1.79  tff(c_849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_847])).
% 4.37/1.79  tff(c_850, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 4.37/1.79  tff(c_851, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.37/1.79  tff(c_1132, plain, (![B_159, A_160]: (v2_tops_1(B_159, A_160) | ~v3_tops_1(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/1.79  tff(c_1143, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1132])).
% 4.37/1.79  tff(c_1148, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_851, c_1143])).
% 4.37/1.79  tff(c_1424, plain, (![B_188, A_189]: (r1_tarski(B_188, k2_tops_1(A_189, B_188)) | ~v2_tops_1(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.37/1.79  tff(c_1432, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1424])).
% 4.37/1.79  tff(c_1437, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1148, c_1432])).
% 4.37/1.79  tff(c_915, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=k3_subset_1(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.37/1.79  tff(c_926, plain, (![B_14, A_13]: (k4_xboole_0(B_14, A_13)=k3_subset_1(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_915])).
% 4.37/1.79  tff(c_1097, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1084, c_926])).
% 4.37/1.79  tff(c_970, plain, (![A_144, B_145, C_146]: (k7_subset_1(A_144, B_145, C_146)=k4_xboole_0(B_145, C_146) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.37/1.79  tff(c_979, plain, (![C_146]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_146)=k4_xboole_0('#skF_2', C_146))), inference(resolution, [status(thm)], [c_38, c_970])).
% 4.37/1.79  tff(c_1203, plain, (![A_165, B_166]: (k2_pre_topc(A_165, B_166)=B_166 | ~v4_pre_topc(B_166, A_165) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.37/1.79  tff(c_1214, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1203])).
% 4.37/1.79  tff(c_1219, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1214])).
% 4.37/1.79  tff(c_2015, plain, (![A_220, B_221]: (k7_subset_1(u1_struct_0(A_220), k2_pre_topc(A_220, B_221), k1_tops_1(A_220, B_221))=k2_tops_1(A_220, B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.37/1.79  tff(c_2028, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1219, c_2015])).
% 4.37/1.79  tff(c_2038, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1097, c_979, c_2028])).
% 4.37/1.79  tff(c_889, plain, (![A_132, B_133]: (m1_subset_1(k3_subset_1(A_132, B_133), k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.79  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.37/1.79  tff(c_894, plain, (![A_134, B_135]: (r1_tarski(k3_subset_1(A_134, B_135), A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_889, c_16])).
% 4.37/1.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.79  tff(c_900, plain, (![A_134, B_135]: (k3_subset_1(A_134, B_135)=A_134 | ~r1_tarski(A_134, k3_subset_1(A_134, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_894, c_2])).
% 4.37/1.79  tff(c_2051, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2038, c_900])).
% 4.37/1.79  tff(c_2071, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_2038, c_2051])).
% 4.37/1.79  tff(c_2072, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_850, c_2071])).
% 4.37/1.79  tff(c_2079, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_2072])).
% 4.37/1.79  tff(c_2083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1084, c_2079])).
% 4.37/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.79  
% 4.37/1.79  Inference rules
% 4.37/1.79  ----------------------
% 4.37/1.79  #Ref     : 0
% 4.37/1.79  #Sup     : 468
% 4.37/1.79  #Fact    : 0
% 4.37/1.79  #Define  : 0
% 4.37/1.79  #Split   : 12
% 4.37/1.79  #Chain   : 0
% 4.37/1.79  #Close   : 0
% 4.37/1.79  
% 4.37/1.79  Ordering : KBO
% 4.37/1.79  
% 4.37/1.79  Simplification rules
% 4.37/1.79  ----------------------
% 4.37/1.79  #Subsume      : 79
% 4.37/1.79  #Demod        : 153
% 4.37/1.79  #Tautology    : 147
% 4.37/1.79  #SimpNegUnit  : 6
% 4.37/1.79  #BackRed      : 1
% 4.37/1.79  
% 4.37/1.79  #Partial instantiations: 0
% 4.37/1.79  #Strategies tried      : 1
% 4.37/1.79  
% 4.37/1.79  Timing (in seconds)
% 4.37/1.79  ----------------------
% 4.37/1.80  Preprocessing        : 0.34
% 4.37/1.80  Parsing              : 0.18
% 4.37/1.80  CNF conversion       : 0.02
% 4.37/1.80  Main loop            : 0.69
% 4.37/1.80  Inferencing          : 0.24
% 4.37/1.80  Reduction            : 0.21
% 4.37/1.80  Demodulation         : 0.14
% 4.37/1.80  BG Simplification    : 0.03
% 4.37/1.80  Subsumption          : 0.15
% 4.37/1.80  Abstraction          : 0.04
% 4.37/1.80  MUC search           : 0.00
% 4.37/1.80  Cooper               : 0.00
% 4.37/1.80  Total                : 1.06
% 4.37/1.80  Index Insertion      : 0.00
% 4.37/1.80  Index Deletion       : 0.00
% 4.37/1.80  Index Matching       : 0.00
% 4.37/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
