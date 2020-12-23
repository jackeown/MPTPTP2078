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
% DateTime   : Thu Dec  3 10:20:55 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 200 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_66,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,C_40) = k3_xboole_0(B_39,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_606,plain,(
    ! [A_88,B_89,B_90] :
      ( k9_subset_1(A_88,B_89,k3_subset_1(A_88,B_90)) = k3_xboole_0(B_89,k3_subset_1(A_88,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_628,plain,(
    ! [B_91] : k9_subset_1(u1_struct_0('#skF_1'),B_91,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(B_91,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_606])).

tff(c_158,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k9_subset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_171,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k9_subset_1(A_47,B_48,C_49),A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_158,c_16])).

tff(c_634,plain,(
    ! [B_91] :
      ( r1_tarski(k3_xboole_0(B_91,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_171])).

tff(c_869,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_872,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_8,c_869])).

tff(c_879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_872])).

tff(c_881,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_561,plain,(
    ! [A_85,B_86] :
      ( k2_tops_1(A_85,k3_subset_1(u1_struct_0(A_85),B_86)) = k2_tops_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_579,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_561])).

tff(c_592,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_579])).

tff(c_126,plain,(
    ! [B_39] : k9_subset_1(u1_struct_0('#skF_1'),B_39,'#skF_2') = k3_xboole_0(B_39,'#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_30,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_226,plain,(
    ! [A_59,B_60] :
      ( k2_pre_topc(A_59,B_60) = B_60
      | ~ v4_pre_topc(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_244,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_226])).

tff(c_253,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_244])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_809,plain,(
    ! [A_103,B_104] :
      ( k9_subset_1(u1_struct_0(A_103),k2_pre_topc(A_103,B_104),k2_pre_topc(A_103,k3_subset_1(u1_struct_0(A_103),B_104))) = k2_tops_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_845,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k2_pre_topc('#skF_1','#skF_2')) = k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_809])).

tff(c_853,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_592,c_126,c_253,c_845])).

tff(c_1788,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_853])).

tff(c_147,plain,(
    ! [B_44,B_45,A_46] :
      ( k9_subset_1(B_44,B_45,A_46) = k3_xboole_0(B_45,A_46)
      | ~ r1_tarski(A_46,B_44) ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_157,plain,(
    ! [B_2,B_45] : k9_subset_1(B_2,B_45,B_2) = k3_xboole_0(B_45,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_204,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(k9_subset_1(A_54,B_55,C_56),A_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_158,c_16])).

tff(c_211,plain,(
    ! [B_45,B_2] :
      ( r1_tarski(k3_xboole_0(B_45,B_2),B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_204])).

tff(c_1842,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_211])).

tff(c_1862,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1842])).

tff(c_1866,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1862])).

tff(c_1870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.60  
% 3.62/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.60  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.62/1.60  
% 3.62/1.60  %Foreground sorts:
% 3.62/1.60  
% 3.62/1.60  
% 3.62/1.60  %Background operators:
% 3.62/1.60  
% 3.62/1.60  
% 3.62/1.60  %Foreground operators:
% 3.62/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.60  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.62/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.62/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.62/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.62/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.62/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.62/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.60  
% 3.62/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.62/1.62  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.62/1.62  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 3.62/1.62  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.62/1.62  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.62/1.62  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.62/1.62  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 3.62/1.62  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.62/1.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.62/1.62  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_1)).
% 3.62/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.62  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.62/1.62  tff(c_28, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.62  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.62  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.62  tff(c_117, plain, (![A_38, B_39, C_40]: (k9_subset_1(A_38, B_39, C_40)=k3_xboole_0(B_39, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.62/1.62  tff(c_606, plain, (![A_88, B_89, B_90]: (k9_subset_1(A_88, B_89, k3_subset_1(A_88, B_90))=k3_xboole_0(B_89, k3_subset_1(A_88, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_8, c_117])).
% 3.62/1.62  tff(c_628, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_1'), B_91, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(B_91, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_32, c_606])).
% 3.62/1.62  tff(c_158, plain, (![A_47, B_48, C_49]: (m1_subset_1(k9_subset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.62  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.62/1.62  tff(c_171, plain, (![A_47, B_48, C_49]: (r1_tarski(k9_subset_1(A_47, B_48, C_49), A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_158, c_16])).
% 3.62/1.62  tff(c_634, plain, (![B_91]: (r1_tarski(k3_xboole_0(B_91, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_628, c_171])).
% 3.62/1.62  tff(c_869, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_634])).
% 3.62/1.62  tff(c_872, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_8, c_869])).
% 3.62/1.62  tff(c_879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_872])).
% 3.62/1.62  tff(c_881, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_634])).
% 3.62/1.62  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.62  tff(c_561, plain, (![A_85, B_86]: (k2_tops_1(A_85, k3_subset_1(u1_struct_0(A_85), B_86))=k2_tops_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.62  tff(c_579, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_561])).
% 3.62/1.62  tff(c_592, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_579])).
% 3.62/1.62  tff(c_126, plain, (![B_39]: (k9_subset_1(u1_struct_0('#skF_1'), B_39, '#skF_2')=k3_xboole_0(B_39, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_117])).
% 3.62/1.62  tff(c_30, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.62  tff(c_226, plain, (![A_59, B_60]: (k2_pre_topc(A_59, B_60)=B_60 | ~v4_pre_topc(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.62  tff(c_244, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_226])).
% 3.62/1.62  tff(c_253, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_244])).
% 3.62/1.62  tff(c_58, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.62  tff(c_64, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_58])).
% 3.62/1.62  tff(c_809, plain, (![A_103, B_104]: (k9_subset_1(u1_struct_0(A_103), k2_pre_topc(A_103, B_104), k2_pre_topc(A_103, k3_subset_1(u1_struct_0(A_103), B_104)))=k2_tops_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.62/1.62  tff(c_845, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_809])).
% 3.62/1.62  tff(c_853, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_592, c_126, c_253, c_845])).
% 3.62/1.62  tff(c_1788, plain, (k3_xboole_0(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_881, c_853])).
% 3.62/1.62  tff(c_147, plain, (![B_44, B_45, A_46]: (k9_subset_1(B_44, B_45, A_46)=k3_xboole_0(B_45, A_46) | ~r1_tarski(A_46, B_44))), inference(resolution, [status(thm)], [c_18, c_117])).
% 3.62/1.62  tff(c_157, plain, (![B_2, B_45]: (k9_subset_1(B_2, B_45, B_2)=k3_xboole_0(B_45, B_2))), inference(resolution, [status(thm)], [c_6, c_147])).
% 3.62/1.62  tff(c_204, plain, (![A_54, B_55, C_56]: (r1_tarski(k9_subset_1(A_54, B_55, C_56), A_54) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_158, c_16])).
% 3.62/1.62  tff(c_211, plain, (![B_45, B_2]: (r1_tarski(k3_xboole_0(B_45, B_2), B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_204])).
% 3.62/1.62  tff(c_1842, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1788, c_211])).
% 3.62/1.62  tff(c_1862, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_1842])).
% 3.62/1.62  tff(c_1866, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_1862])).
% 3.62/1.62  tff(c_1870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1866])).
% 3.62/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.62  
% 3.62/1.62  Inference rules
% 3.62/1.62  ----------------------
% 3.62/1.62  #Ref     : 0
% 3.62/1.62  #Sup     : 427
% 3.62/1.62  #Fact    : 0
% 3.62/1.62  #Define  : 0
% 3.62/1.62  #Split   : 6
% 3.62/1.62  #Chain   : 0
% 3.62/1.62  #Close   : 0
% 3.62/1.62  
% 3.62/1.62  Ordering : KBO
% 3.62/1.62  
% 3.62/1.62  Simplification rules
% 3.62/1.62  ----------------------
% 3.62/1.62  #Subsume      : 43
% 3.62/1.62  #Demod        : 269
% 3.62/1.62  #Tautology    : 153
% 3.62/1.62  #SimpNegUnit  : 1
% 3.62/1.62  #BackRed      : 0
% 3.62/1.62  
% 3.62/1.62  #Partial instantiations: 0
% 3.62/1.62  #Strategies tried      : 1
% 3.62/1.62  
% 3.62/1.62  Timing (in seconds)
% 3.62/1.62  ----------------------
% 3.62/1.62  Preprocessing        : 0.30
% 3.62/1.62  Parsing              : 0.16
% 3.62/1.62  CNF conversion       : 0.02
% 3.62/1.62  Main loop            : 0.56
% 3.62/1.62  Inferencing          : 0.20
% 3.62/1.62  Reduction            : 0.19
% 3.62/1.62  Demodulation         : 0.15
% 3.62/1.62  BG Simplification    : 0.03
% 3.62/1.62  Subsumption          : 0.11
% 3.62/1.62  Abstraction          : 0.04
% 3.62/1.62  MUC search           : 0.00
% 3.62/1.62  Cooper               : 0.00
% 3.62/1.62  Total                : 0.89
% 3.62/1.62  Index Insertion      : 0.00
% 3.62/1.62  Index Deletion       : 0.00
% 3.62/1.62  Index Matching       : 0.00
% 3.62/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
