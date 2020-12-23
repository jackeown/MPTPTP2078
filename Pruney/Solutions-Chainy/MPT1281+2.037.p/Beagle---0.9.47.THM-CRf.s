%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:18 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 258 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 618 expanded)
%              Number of equality atoms :   13 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_38,B_39] :
      ( k2_pre_topc(A_38,k1_tops_1(A_38,B_39)) = B_39
      | ~ v5_tops_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_76,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_83,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_76])).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_24])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k1_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_35,plain,(
    ! [A_36,B_37] :
      ( k2_pre_topc(A_36,k2_pre_topc(A_36,B_37)) = k2_pre_topc(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [A_51,B_52] :
      ( k2_pre_topc(A_51,k2_pre_topc(A_51,k1_tops_1(A_51,B_52))) = k2_pre_topc(A_51,k1_tops_1(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_123,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_130,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_83,c_83,c_123])).

tff(c_141,plain,(
    ! [A_53,B_54] :
      ( k9_subset_1(u1_struct_0(A_53),k2_pre_topc(A_53,B_54),k2_pre_topc(A_53,k3_subset_1(u1_struct_0(A_53),B_54))) = k2_tops_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_156,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_141])).

tff(c_163,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_156])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_172,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_4])).

tff(c_178,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_181,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_178])).

tff(c_184,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_181])).

tff(c_187,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_187])).

tff(c_193,plain,(
    m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_192,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_106,plain,(
    ! [A_48,B_49,C_50] :
      ( r1_tarski(k3_subset_1(A_48,B_49),k3_subset_1(A_48,k9_subset_1(A_48,B_49,C_50)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_7,C_9,A_6] :
      ( r1_tarski(B_7,C_9)
      | ~ r1_tarski(k3_subset_1(A_6,C_9),k3_subset_1(A_6,B_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_300,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k9_subset_1(A_57,B_58,C_59),B_58)
      | ~ m1_subset_1(k9_subset_1(A_57,B_58,C_59),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_106,c_6])).

tff(c_302,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))),'#skF_2')
    | ~ m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_300])).

tff(c_308,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_193,c_192,c_163,c_302])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  %$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.23/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.23/1.25  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.25  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.25  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.23/1.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.23/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.25  
% 2.23/1.27  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) => r1_tarski(k2_tops_1(A, B), k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tops_1)).
% 2.23/1.27  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.23/1.27  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.23/1.27  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.23/1.27  tff(f_83, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.23/1.27  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 2.23/1.27  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_1)).
% 2.23/1.27  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.23/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.23/1.27  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.23/1.27  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_26, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_64, plain, (![A_38, B_39]: (k2_pre_topc(A_38, k1_tops_1(A_38, B_39))=B_39 | ~v5_tops_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.27  tff(c_76, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~v5_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.23/1.27  tff(c_83, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_76])).
% 2.23/1.27  tff(c_24, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_84, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_24])).
% 2.23/1.27  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.27  tff(c_12, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.27  tff(c_22, plain, (![A_24, B_25]: (m1_subset_1(k1_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.23/1.27  tff(c_35, plain, (![A_36, B_37]: (k2_pre_topc(A_36, k2_pre_topc(A_36, B_37))=k2_pre_topc(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.27  tff(c_111, plain, (![A_51, B_52]: (k2_pre_topc(A_51, k2_pre_topc(A_51, k1_tops_1(A_51, B_52)))=k2_pre_topc(A_51, k1_tops_1(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.23/1.27  tff(c_123, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_111])).
% 2.23/1.27  tff(c_130, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_83, c_83, c_123])).
% 2.23/1.27  tff(c_141, plain, (![A_53, B_54]: (k9_subset_1(u1_struct_0(A_53), k2_pre_topc(A_53, B_54), k2_pre_topc(A_53, k3_subset_1(u1_struct_0(A_53), B_54)))=k2_tops_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.27  tff(c_156, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_130, c_141])).
% 2.23/1.27  tff(c_163, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_156])).
% 2.23/1.27  tff(c_4, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.27  tff(c_172, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_4])).
% 2.23/1.27  tff(c_178, plain, (~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_172])).
% 2.23/1.27  tff(c_181, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_178])).
% 2.23/1.27  tff(c_184, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_181])).
% 2.23/1.27  tff(c_187, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_184])).
% 2.23/1.27  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_187])).
% 2.23/1.27  tff(c_193, plain, (m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_172])).
% 2.23/1.27  tff(c_192, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_172])).
% 2.23/1.27  tff(c_106, plain, (![A_48, B_49, C_50]: (r1_tarski(k3_subset_1(A_48, B_49), k3_subset_1(A_48, k9_subset_1(A_48, B_49, C_50))) | ~m1_subset_1(C_50, k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.27  tff(c_6, plain, (![B_7, C_9, A_6]: (r1_tarski(B_7, C_9) | ~r1_tarski(k3_subset_1(A_6, C_9), k3_subset_1(A_6, B_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.27  tff(c_300, plain, (![A_57, B_58, C_59]: (r1_tarski(k9_subset_1(A_57, B_58, C_59), B_58) | ~m1_subset_1(k9_subset_1(A_57, B_58, C_59), k1_zfmisc_1(A_57)) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_106, c_6])).
% 2.23/1.27  tff(c_302, plain, (r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), '#skF_2') | ~m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_300])).
% 2.23/1.27  tff(c_308, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_193, c_192, c_163, c_302])).
% 2.23/1.27  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_308])).
% 2.23/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  Inference rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Ref     : 0
% 2.23/1.27  #Sup     : 64
% 2.23/1.27  #Fact    : 0
% 2.23/1.27  #Define  : 0
% 2.23/1.27  #Split   : 4
% 2.23/1.27  #Chain   : 0
% 2.23/1.27  #Close   : 0
% 2.23/1.27  
% 2.23/1.27  Ordering : KBO
% 2.23/1.27  
% 2.23/1.27  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 0
% 2.23/1.27  #Demod        : 53
% 2.23/1.27  #Tautology    : 22
% 2.23/1.27  #SimpNegUnit  : 1
% 2.23/1.27  #BackRed      : 1
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.29
% 2.23/1.27  Parsing              : 0.17
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.27  Main loop            : 0.22
% 2.23/1.27  Inferencing          : 0.08
% 2.23/1.27  Reduction            : 0.07
% 2.23/1.27  Demodulation         : 0.05
% 2.23/1.27  BG Simplification    : 0.02
% 2.23/1.27  Subsumption          : 0.04
% 2.23/1.27  Abstraction          : 0.01
% 2.23/1.27  MUC search           : 0.00
% 2.23/1.27  Cooper               : 0.00
% 2.23/1.27  Total                : 0.55
% 2.23/1.27  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
