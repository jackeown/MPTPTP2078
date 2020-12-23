%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:48 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 152 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101))))
      | ~ r1_tarski(C_100,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101))))
      | ~ l1_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_239,plain,(
    ! [A_103,B_104,A_105] :
      ( m1_subset_1(k4_xboole_0(A_103,B_104),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | ~ m1_subset_1(A_103,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | ~ l1_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36] :
      ( k9_subset_1(A_34,B_35,C_36) = k3_xboole_0(B_35,C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_458,plain,(
    ! [A_125,B_126,A_127,B_128] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(A_125)),B_126,k4_xboole_0(A_127,B_128)) = k3_xboole_0(B_126,k4_xboole_0(A_127,B_128))
      | ~ m1_subset_1(A_127,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_struct_0(A_125) ) ),
    inference(resolution,[status(thm)],[c_239,c_20])).

tff(c_469,plain,(
    ! [B_126,B_128] :
      ( k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_126,k4_xboole_0('#skF_3',B_128)) = k3_xboole_0(B_126,k4_xboole_0('#skF_3',B_128))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_458])).

tff(c_471,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_507,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_471])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_507])).

tff(c_513,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_32,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_238,plain,(
    ! [A_3,B_4,A_101] :
      ( m1_subset_1(k4_xboole_0(A_3,B_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101))))
      | ~ m1_subset_1(A_3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101))))
      | ~ l1_struct_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_370,plain,(
    ! [B_120,A_121,C_122] :
      ( v1_tops_2(B_120,A_121)
      | ~ v1_tops_2(C_122,A_121)
      | ~ r1_tarski(B_120,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121))))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121))))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_625,plain,(
    ! [A_140,B_141,A_142] :
      ( v1_tops_2(k4_xboole_0(A_140,B_141),A_142)
      | ~ v1_tops_2(A_140,A_142)
      | ~ m1_subset_1(A_140,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142))))
      | ~ m1_subset_1(k4_xboole_0(A_140,B_141),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142))))
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_370])).

tff(c_659,plain,(
    ! [A_143,B_144,A_145] :
      ( v1_tops_2(k4_xboole_0(A_143,B_144),A_145)
      | ~ v1_tops_2(A_143,A_145)
      | ~ l1_pre_topc(A_145)
      | ~ m1_subset_1(A_143,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_238,c_625])).

tff(c_667,plain,(
    ! [B_144] :
      ( v1_tops_2(k4_xboole_0('#skF_2',B_144),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_659])).

tff(c_676,plain,(
    ! [B_146] : v1_tops_2(k4_xboole_0('#skF_2',B_146),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_38,c_32,c_667])).

tff(c_704,plain,(
    ! [B_6] : v1_tops_2(k3_xboole_0('#skF_2',B_6),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_676])).

tff(c_113,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,C_78) = k3_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [B_77] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_77,'#skF_3') = k3_xboole_0(B_77,'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_30,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    ~ v1_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_30])).

tff(c_708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:37:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.44  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.44  
% 2.97/1.44  %Foreground sorts:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Background operators:
% 2.97/1.44  
% 2.97/1.44  
% 2.97/1.44  %Foreground operators:
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.97/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.97/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.97/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.44  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.97/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.97/1.44  
% 2.97/1.46  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.97/1.46  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tops_2)).
% 2.97/1.46  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.97/1.46  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.97/1.46  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 2.97/1.46  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.97/1.46  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 2.97/1.46  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.46  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.46  tff(c_24, plain, (![A_39]: (l1_struct_0(A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.46  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.46  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.46  tff(c_232, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101)))) | ~r1_tarski(C_100, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101)))) | ~l1_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.46  tff(c_239, plain, (![A_103, B_104, A_105]: (m1_subset_1(k4_xboole_0(A_103, B_104), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105)))) | ~m1_subset_1(A_103, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105)))) | ~l1_struct_0(A_105))), inference(resolution, [status(thm)], [c_4, c_232])).
% 2.97/1.46  tff(c_20, plain, (![A_34, B_35, C_36]: (k9_subset_1(A_34, B_35, C_36)=k3_xboole_0(B_35, C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.46  tff(c_458, plain, (![A_125, B_126, A_127, B_128]: (k9_subset_1(k1_zfmisc_1(u1_struct_0(A_125)), B_126, k4_xboole_0(A_127, B_128))=k3_xboole_0(B_126, k4_xboole_0(A_127, B_128)) | ~m1_subset_1(A_127, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_struct_0(A_125))), inference(resolution, [status(thm)], [c_239, c_20])).
% 2.97/1.46  tff(c_469, plain, (![B_126, B_128]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_126, k4_xboole_0('#skF_3', B_128))=k3_xboole_0(B_126, k4_xboole_0('#skF_3', B_128)) | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_458])).
% 2.97/1.46  tff(c_471, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_469])).
% 2.97/1.46  tff(c_507, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_471])).
% 2.97/1.46  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_507])).
% 2.97/1.46  tff(c_513, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_469])).
% 2.97/1.46  tff(c_32, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.46  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.46  tff(c_238, plain, (![A_3, B_4, A_101]: (m1_subset_1(k4_xboole_0(A_3, B_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101)))) | ~m1_subset_1(A_3, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_101)))) | ~l1_struct_0(A_101))), inference(resolution, [status(thm)], [c_4, c_232])).
% 2.97/1.46  tff(c_370, plain, (![B_120, A_121, C_122]: (v1_tops_2(B_120, A_121) | ~v1_tops_2(C_122, A_121) | ~r1_tarski(B_120, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121)))) | ~m1_subset_1(B_120, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_121)))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.97/1.46  tff(c_625, plain, (![A_140, B_141, A_142]: (v1_tops_2(k4_xboole_0(A_140, B_141), A_142) | ~v1_tops_2(A_140, A_142) | ~m1_subset_1(A_140, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142)))) | ~m1_subset_1(k4_xboole_0(A_140, B_141), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_142)))) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_4, c_370])).
% 2.97/1.46  tff(c_659, plain, (![A_143, B_144, A_145]: (v1_tops_2(k4_xboole_0(A_143, B_144), A_145) | ~v1_tops_2(A_143, A_145) | ~l1_pre_topc(A_145) | ~m1_subset_1(A_143, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~l1_struct_0(A_145))), inference(resolution, [status(thm)], [c_238, c_625])).
% 2.97/1.46  tff(c_667, plain, (![B_144]: (v1_tops_2(k4_xboole_0('#skF_2', B_144), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_659])).
% 2.97/1.46  tff(c_676, plain, (![B_146]: (v1_tops_2(k4_xboole_0('#skF_2', B_146), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_38, c_32, c_667])).
% 2.97/1.46  tff(c_704, plain, (![B_6]: (v1_tops_2(k3_xboole_0('#skF_2', B_6), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_676])).
% 2.97/1.46  tff(c_113, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, C_78)=k3_xboole_0(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.46  tff(c_118, plain, (![B_77]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_77, '#skF_3')=k3_xboole_0(B_77, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_113])).
% 2.97/1.46  tff(c_30, plain, (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.46  tff(c_120, plain, (~v1_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_30])).
% 2.97/1.46  tff(c_708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_704, c_120])).
% 2.97/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.46  
% 2.97/1.46  Inference rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Ref     : 0
% 2.97/1.46  #Sup     : 160
% 2.97/1.46  #Fact    : 0
% 2.97/1.46  #Define  : 0
% 2.97/1.46  #Split   : 2
% 2.97/1.46  #Chain   : 0
% 2.97/1.46  #Close   : 0
% 2.97/1.46  
% 2.97/1.46  Ordering : KBO
% 2.97/1.46  
% 2.97/1.46  Simplification rules
% 2.97/1.46  ----------------------
% 2.97/1.46  #Subsume      : 7
% 2.97/1.46  #Demod        : 92
% 2.97/1.46  #Tautology    : 78
% 2.97/1.46  #SimpNegUnit  : 0
% 2.97/1.46  #BackRed      : 2
% 2.97/1.46  
% 2.97/1.46  #Partial instantiations: 0
% 2.97/1.46  #Strategies tried      : 1
% 2.97/1.46  
% 2.97/1.46  Timing (in seconds)
% 2.97/1.46  ----------------------
% 2.97/1.46  Preprocessing        : 0.34
% 2.97/1.46  Parsing              : 0.18
% 2.97/1.46  CNF conversion       : 0.02
% 2.97/1.46  Main loop            : 0.35
% 2.97/1.46  Inferencing          : 0.13
% 2.97/1.46  Reduction            : 0.13
% 3.15/1.46  Demodulation         : 0.10
% 3.15/1.46  BG Simplification    : 0.02
% 3.15/1.46  Subsumption          : 0.05
% 3.15/1.46  Abstraction          : 0.03
% 3.15/1.46  MUC search           : 0.00
% 3.15/1.46  Cooper               : 0.00
% 3.15/1.46  Total                : 0.73
% 3.15/1.46  Index Insertion      : 0.00
% 3.15/1.46  Index Deletion       : 0.00
% 3.15/1.46  Index Matching       : 0.00
% 3.15/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
