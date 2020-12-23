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
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 122 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 396 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_33,plain,(
    ! [A_32,B_33,C_34] :
      ( k9_subset_1(A_32,B_33,C_34) = k3_xboole_0(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [B_33] : k9_subset_1(u1_struct_0('#skF_1'),B_33,'#skF_3') = k3_xboole_0(B_33,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_49,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_18])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_81,plain,(
    ! [B_42,A_43] :
      ( v4_pre_topc(B_42,A_43)
      | ~ v2_compts_1(B_42,A_43)
      | ~ v8_pre_topc(A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_107,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_94])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_97,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_81])).

tff(c_110,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_97])).

tff(c_293,plain,(
    ! [B_84,C_85,A_86] :
      ( v4_pre_topc(k3_xboole_0(B_84,C_85),A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ v4_pre_topc(C_85,A_86)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ v4_pre_topc(B_84,A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_312,plain,(
    ! [B_84] :
      ( v4_pre_topc(k3_xboole_0(B_84,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_84,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_293])).

tff(c_435,plain,(
    ! [B_96] :
      ( v4_pre_topc(k3_xboole_0(B_96,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_96,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_110,c_312])).

tff(c_460,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_435])).

tff(c_473,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_460])).

tff(c_59,plain,(
    ! [A_37,B_38,C_39] :
      ( m1_subset_1(k9_subset_1(A_37,B_38,C_39),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [B_33] :
      ( m1_subset_1(k3_xboole_0(B_33,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_59])).

tff(c_70,plain,(
    ! [B_33] : m1_subset_1(k3_xboole_0(B_33,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_251,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k3_subset_1(A_80,B_81),k3_subset_1(A_80,k9_subset_1(A_80,B_81,C_82)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_269,plain,(
    ! [B_33] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),B_33),k3_subset_1(u1_struct_0('#skF_1'),k3_xboole_0(B_33,'#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_251])).

tff(c_286,plain,(
    ! [B_83] :
      ( r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),B_83),k3_subset_1(u1_struct_0('#skF_1'),k3_xboole_0(B_83,'#skF_3')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_269])).

tff(c_6,plain,(
    ! [B_8,C_10,A_7] :
      ( r1_tarski(B_8,C_10)
      | ~ r1_tarski(k3_subset_1(A_7,C_10),k3_subset_1(A_7,B_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_289,plain,(
    ! [B_83] :
      ( r1_tarski(k3_xboole_0(B_83,'#skF_3'),B_83)
      | ~ m1_subset_1(k3_xboole_0(B_83,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_286,c_6])).

tff(c_338,plain,(
    ! [B_87] :
      ( r1_tarski(k3_xboole_0(B_87,'#skF_3'),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_289])).

tff(c_365,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_338])).

tff(c_412,plain,(
    ! [C_92,A_93,B_94] :
      ( v2_compts_1(C_92,A_93)
      | ~ v4_pre_topc(C_92,A_93)
      | ~ r1_tarski(C_92,B_94)
      | ~ v2_compts_1(B_94,A_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_706,plain,(
    ! [A_140] :
      ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),A_140)
      | ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),A_140)
      | ~ v2_compts_1('#skF_2',A_140)
      | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_365,c_412])).

tff(c_710,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_706])).

tff(c_713,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_22,c_473,c_710])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.99  
% 3.75/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.99  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.75/1.99  
% 3.75/1.99  %Foreground sorts:
% 3.75/1.99  
% 3.75/1.99  
% 3.75/1.99  %Background operators:
% 3.75/1.99  
% 3.75/1.99  
% 3.75/1.99  %Foreground operators:
% 3.75/1.99  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.75/1.99  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.75/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.75/1.99  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.99  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.99  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.99  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.75/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.75/1.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.75/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.99  
% 3.75/2.00  tff(f_113, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.75/2.00  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.75/2.00  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.75/2.00  tff(f_63, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tops_1)).
% 3.75/2.00  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.75/2.00  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 3.75/2.00  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.75/2.00  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.75/2.00  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_33, plain, (![A_32, B_33, C_34]: (k9_subset_1(A_32, B_33, C_34)=k3_xboole_0(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.75/2.00  tff(c_39, plain, (![B_33]: (k9_subset_1(u1_struct_0('#skF_1'), B_33, '#skF_3')=k3_xboole_0(B_33, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_33])).
% 3.75/2.00  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_49, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_18])).
% 3.75/2.00  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_81, plain, (![B_42, A_43]: (v4_pre_topc(B_42, A_43) | ~v2_compts_1(B_42, A_43) | ~v8_pre_topc(A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.75/2.00  tff(c_94, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_81])).
% 3.75/2.00  tff(c_107, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_94])).
% 3.75/2.00  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.75/2.00  tff(c_97, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_81])).
% 3.75/2.00  tff(c_110, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_97])).
% 3.75/2.00  tff(c_293, plain, (![B_84, C_85, A_86]: (v4_pre_topc(k3_xboole_0(B_84, C_85), A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~v4_pre_topc(C_85, A_86) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_86))) | ~v4_pre_topc(B_84, A_86) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.75/2.00  tff(c_312, plain, (![B_84]: (v4_pre_topc(k3_xboole_0(B_84, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_84, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_293])).
% 3.75/2.00  tff(c_435, plain, (![B_96]: (v4_pre_topc(k3_xboole_0(B_96, '#skF_3'), '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_96, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_110, c_312])).
% 3.75/2.00  tff(c_460, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_435])).
% 3.75/2.00  tff(c_473, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_460])).
% 3.75/2.00  tff(c_59, plain, (![A_37, B_38, C_39]: (m1_subset_1(k9_subset_1(A_37, B_38, C_39), k1_zfmisc_1(A_37)) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.75/2.00  tff(c_64, plain, (![B_33]: (m1_subset_1(k3_xboole_0(B_33, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_39, c_59])).
% 3.75/2.00  tff(c_70, plain, (![B_33]: (m1_subset_1(k3_xboole_0(B_33, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_64])).
% 3.75/2.00  tff(c_251, plain, (![A_80, B_81, C_82]: (r1_tarski(k3_subset_1(A_80, B_81), k3_subset_1(A_80, k9_subset_1(A_80, B_81, C_82))) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.75/2.00  tff(c_269, plain, (![B_33]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), B_33), k3_subset_1(u1_struct_0('#skF_1'), k3_xboole_0(B_33, '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_39, c_251])).
% 3.75/2.00  tff(c_286, plain, (![B_83]: (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), B_83), k3_subset_1(u1_struct_0('#skF_1'), k3_xboole_0(B_83, '#skF_3'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_269])).
% 3.75/2.00  tff(c_6, plain, (![B_8, C_10, A_7]: (r1_tarski(B_8, C_10) | ~r1_tarski(k3_subset_1(A_7, C_10), k3_subset_1(A_7, B_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.75/2.00  tff(c_289, plain, (![B_83]: (r1_tarski(k3_xboole_0(B_83, '#skF_3'), B_83) | ~m1_subset_1(k3_xboole_0(B_83, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_286, c_6])).
% 3.75/2.00  tff(c_338, plain, (![B_87]: (r1_tarski(k3_xboole_0(B_87, '#skF_3'), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_289])).
% 3.75/2.00  tff(c_365, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_338])).
% 3.75/2.00  tff(c_412, plain, (![C_92, A_93, B_94]: (v2_compts_1(C_92, A_93) | ~v4_pre_topc(C_92, A_93) | ~r1_tarski(C_92, B_94) | ~v2_compts_1(B_94, A_93) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/2.00  tff(c_706, plain, (![A_140]: (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), A_140) | ~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), A_140) | ~v2_compts_1('#skF_2', A_140) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140))), inference(resolution, [status(thm)], [c_365, c_412])).
% 3.75/2.00  tff(c_710, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_706])).
% 3.75/2.00  tff(c_713, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_22, c_473, c_710])).
% 3.75/2.00  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_713])).
% 3.75/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/2.00  
% 3.75/2.00  Inference rules
% 3.75/2.00  ----------------------
% 3.75/2.00  #Ref     : 0
% 3.75/2.00  #Sup     : 149
% 3.75/2.00  #Fact    : 0
% 3.75/2.00  #Define  : 0
% 3.75/2.00  #Split   : 0
% 3.75/2.00  #Chain   : 0
% 3.75/2.00  #Close   : 0
% 3.75/2.00  
% 3.75/2.00  Ordering : KBO
% 3.75/2.00  
% 3.75/2.00  Simplification rules
% 3.75/2.00  ----------------------
% 3.75/2.00  #Subsume      : 13
% 3.75/2.00  #Demod        : 172
% 3.75/2.00  #Tautology    : 17
% 3.75/2.00  #SimpNegUnit  : 1
% 3.75/2.00  #BackRed      : 1
% 3.75/2.00  
% 3.75/2.00  #Partial instantiations: 0
% 3.75/2.00  #Strategies tried      : 1
% 3.75/2.00  
% 3.75/2.00  Timing (in seconds)
% 3.75/2.00  ----------------------
% 3.75/2.00  Preprocessing        : 0.48
% 3.75/2.01  Parsing              : 0.26
% 3.75/2.01  CNF conversion       : 0.04
% 3.75/2.01  Main loop            : 0.62
% 3.75/2.01  Inferencing          : 0.23
% 3.75/2.01  Reduction            : 0.22
% 3.75/2.01  Demodulation         : 0.16
% 3.75/2.01  BG Simplification    : 0.03
% 3.75/2.01  Subsumption          : 0.10
% 3.75/2.01  Abstraction          : 0.04
% 3.75/2.01  MUC search           : 0.00
% 3.75/2.01  Cooper               : 0.00
% 3.75/2.01  Total                : 1.14
% 3.75/2.01  Index Insertion      : 0.00
% 3.75/2.01  Index Deletion       : 0.00
% 3.75/2.01  Index Matching       : 0.00
% 3.75/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
