%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:05 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 125 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 228 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_115,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_3') = k3_xboole_0(B_58,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [B_58] :
      ( m1_subset_1(k3_xboole_0(B_58,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_10])).

tff(c_132,plain,(
    ! [B_58] : m1_subset_1(k3_xboole_0(B_58,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_124])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_94,plain,(
    ! [A_54,B_55] : k9_subset_1(A_54,B_55,A_54) = k3_xboole_0(B_55,A_54) ),
    inference(resolution,[status(thm)],[c_31,c_78])).

tff(c_71,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k9_subset_1(A_42,B_43,C_44),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k9_subset_1(A_42,B_43,C_44),A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_71,c_16])).

tff(c_100,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k3_xboole_0(B_55,A_54),A_54)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_75])).

tff(c_109,plain,(
    ! [B_55,A_54] : r1_tarski(k3_xboole_0(B_55,A_54),A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_100])).

tff(c_22,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_tarski(k2_pre_topc(A_20,B_24),k2_pre_topc(A_20,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k2_pre_topc(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_585,plain,(
    ! [A_135,B_136,B_137] :
      ( k9_subset_1(u1_struct_0(A_135),B_136,k2_pre_topc(A_135,B_137)) = k3_xboole_0(B_136,k2_pre_topc(A_135,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_173,c_12])).

tff(c_617,plain,(
    ! [B_136] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_136,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_136,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_585])).

tff(c_647,plain,(
    ! [B_136] : k9_subset_1(u1_struct_0('#skF_1'),B_136,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_136,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_617])).

tff(c_91,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_24,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_24])).

tff(c_652,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_114])).

tff(c_686,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_652])).

tff(c_1260,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_686])).

tff(c_1263,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1260])).

tff(c_1267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_132,c_28,c_2,c_1263])).

tff(c_1268,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_1272,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1268])).

tff(c_1276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_132,c_26,c_109,c_1272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.59  
% 3.42/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.60  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.42/1.60  
% 3.42/1.60  %Foreground sorts:
% 3.42/1.60  
% 3.42/1.60  
% 3.42/1.60  %Background operators:
% 3.42/1.60  
% 3.42/1.60  
% 3.42/1.60  %Foreground operators:
% 3.42/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.42/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.42/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.42/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.42/1.60  
% 3.42/1.61  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 3.42/1.61  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.42/1.61  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.42/1.61  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.42/1.61  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.42/1.61  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.42/1.61  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.42/1.61  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.42/1.61  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.42/1.61  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.42/1.61  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.61  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.61  tff(c_78, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.61  tff(c_115, plain, (![B_58]: (k9_subset_1(u1_struct_0('#skF_1'), B_58, '#skF_3')=k3_xboole_0(B_58, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_78])).
% 3.42/1.61  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.61  tff(c_124, plain, (![B_58]: (m1_subset_1(k3_xboole_0(B_58, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_115, c_10])).
% 3.42/1.61  tff(c_132, plain, (![B_58]: (m1_subset_1(k3_xboole_0(B_58, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_124])).
% 3.42/1.61  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.61  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.61  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.42/1.61  tff(c_94, plain, (![A_54, B_55]: (k9_subset_1(A_54, B_55, A_54)=k3_xboole_0(B_55, A_54))), inference(resolution, [status(thm)], [c_31, c_78])).
% 3.42/1.61  tff(c_71, plain, (![A_42, B_43, C_44]: (m1_subset_1(k9_subset_1(A_42, B_43, C_44), k1_zfmisc_1(A_42)) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.61  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.42/1.61  tff(c_75, plain, (![A_42, B_43, C_44]: (r1_tarski(k9_subset_1(A_42, B_43, C_44), A_42) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_71, c_16])).
% 3.42/1.61  tff(c_100, plain, (![B_55, A_54]: (r1_tarski(k3_xboole_0(B_55, A_54), A_54) | ~m1_subset_1(A_54, k1_zfmisc_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_75])).
% 3.42/1.61  tff(c_109, plain, (![B_55, A_54]: (r1_tarski(k3_xboole_0(B_55, A_54), A_54))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_100])).
% 3.42/1.61  tff(c_22, plain, (![A_20, B_24, C_26]: (r1_tarski(k2_pre_topc(A_20, B_24), k2_pre_topc(A_20, C_26)) | ~r1_tarski(B_24, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.42/1.61  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.61  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.61  tff(c_173, plain, (![A_65, B_66]: (m1_subset_1(k2_pre_topc(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.42/1.61  tff(c_12, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.61  tff(c_585, plain, (![A_135, B_136, B_137]: (k9_subset_1(u1_struct_0(A_135), B_136, k2_pre_topc(A_135, B_137))=k3_xboole_0(B_136, k2_pre_topc(A_135, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_173, c_12])).
% 3.42/1.61  tff(c_617, plain, (![B_136]: (k9_subset_1(u1_struct_0('#skF_1'), B_136, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_136, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_585])).
% 3.42/1.61  tff(c_647, plain, (![B_136]: (k9_subset_1(u1_struct_0('#skF_1'), B_136, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_136, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_617])).
% 3.42/1.61  tff(c_91, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_78])).
% 3.42/1.61  tff(c_24, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.42/1.61  tff(c_114, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_24])).
% 3.42/1.61  tff(c_652, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_114])).
% 3.42/1.61  tff(c_686, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_652])).
% 3.42/1.61  tff(c_1260, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_686])).
% 3.42/1.61  tff(c_1263, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1260])).
% 3.42/1.61  tff(c_1267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_132, c_28, c_2, c_1263])).
% 3.42/1.61  tff(c_1268, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_686])).
% 3.42/1.61  tff(c_1272, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1268])).
% 3.42/1.61  tff(c_1276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_132, c_26, c_109, c_1272])).
% 3.42/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.61  
% 3.42/1.61  Inference rules
% 3.42/1.61  ----------------------
% 3.42/1.61  #Ref     : 0
% 3.42/1.61  #Sup     : 274
% 3.42/1.61  #Fact    : 0
% 3.42/1.61  #Define  : 0
% 3.42/1.61  #Split   : 3
% 3.42/1.61  #Chain   : 0
% 3.42/1.61  #Close   : 0
% 3.42/1.61  
% 3.42/1.61  Ordering : KBO
% 3.42/1.61  
% 3.42/1.61  Simplification rules
% 3.42/1.61  ----------------------
% 3.42/1.61  #Subsume      : 2
% 3.42/1.61  #Demod        : 157
% 3.42/1.61  #Tautology    : 129
% 3.42/1.61  #SimpNegUnit  : 0
% 3.42/1.61  #BackRed      : 2
% 3.42/1.61  
% 3.42/1.61  #Partial instantiations: 0
% 3.42/1.61  #Strategies tried      : 1
% 3.42/1.61  
% 3.42/1.61  Timing (in seconds)
% 3.42/1.61  ----------------------
% 3.42/1.61  Preprocessing        : 0.30
% 3.42/1.61  Parsing              : 0.17
% 3.42/1.61  CNF conversion       : 0.02
% 3.42/1.61  Main loop            : 0.54
% 3.42/1.61  Inferencing          : 0.21
% 3.42/1.61  Reduction            : 0.18
% 3.42/1.61  Demodulation         : 0.14
% 3.42/1.61  BG Simplification    : 0.02
% 3.42/1.61  Subsumption          : 0.09
% 3.42/1.61  Abstraction          : 0.04
% 3.42/1.61  MUC search           : 0.00
% 3.42/1.62  Cooper               : 0.00
% 3.42/1.62  Total                : 0.88
% 3.42/1.62  Index Insertion      : 0.00
% 3.42/1.62  Index Deletion       : 0.00
% 3.42/1.62  Index Matching       : 0.00
% 3.42/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
