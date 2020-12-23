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
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 16.73s
% Output     : CNFRefutation 16.73s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 104 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 326 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_124,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,C_52) = k3_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [B_51] : k9_subset_1(u1_struct_0('#skF_1'),B_51,'#skF_3') = k3_xboole_0(B_51,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_134,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_22])).

tff(c_135,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_87,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_87])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_175,plain,(
    ! [B_58,A_59] :
      ( v4_pre_topc(B_58,A_59)
      | ~ v2_compts_1(B_58,A_59)
      | ~ v8_pre_topc(A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_182,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_175])).

tff(c_189,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_182])).

tff(c_185,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_175])).

tff(c_192,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_24,c_185])).

tff(c_208,plain,(
    ! [B_63,C_64,A_65] :
      ( v4_pre_topc(k3_xboole_0(B_63,C_64),A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v4_pre_topc(C_64,A_65)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ v4_pre_topc(B_63,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_215,plain,(
    ! [B_63] :
      ( v4_pre_topc(k3_xboole_0(B_63,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_63,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_553,plain,(
    ! [B_84] :
      ( v4_pre_topc(k3_xboole_0(B_84,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_84,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_192,c_215])).

tff(c_560,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_553])).

tff(c_567,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2,c_560])).

tff(c_110,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(k3_xboole_0(A_44,C_45),B_46)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_2,A_1,B_46] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_46)
      | ~ r1_tarski(A_1,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_475,plain,(
    ! [C_78,A_79,B_80] :
      ( v2_compts_1(C_78,A_79)
      | ~ v4_pre_topc(C_78,A_79)
      | ~ r1_tarski(C_78,B_80)
      | ~ v2_compts_1(B_80,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1483,plain,(
    ! [A_116,B_117,A_118] :
      ( v2_compts_1(k3_xboole_0(A_116,B_117),A_118)
      | ~ v4_pre_topc(k3_xboole_0(A_116,B_117),A_118)
      | ~ v2_compts_1(A_116,A_118)
      | ~ m1_subset_1(k3_xboole_0(A_116,B_117),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(A_116,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_475])).

tff(c_4432,plain,(
    ! [A_201,B_202,A_203] :
      ( v2_compts_1(k3_xboole_0(A_201,B_202),A_203)
      | ~ v4_pre_topc(k3_xboole_0(A_201,B_202),A_203)
      | ~ v2_compts_1(A_201,A_203)
      | ~ m1_subset_1(A_201,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | ~ r1_tarski(k3_xboole_0(A_201,B_202),u1_struct_0(A_203)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1483])).

tff(c_22673,plain,(
    ! [B_303,A_304,A_305] :
      ( v2_compts_1(k3_xboole_0(B_303,A_304),A_305)
      | ~ v4_pre_topc(k3_xboole_0(B_303,A_304),A_305)
      | ~ v2_compts_1(B_303,A_305)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | ~ r1_tarski(A_304,u1_struct_0(A_305)) ) ),
    inference(resolution,[status(thm)],[c_113,c_4432])).

tff(c_22777,plain,
    ( v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_567,c_22673])).

tff(c_22839,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_34,c_30,c_24,c_22777])).

tff(c_22841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_22839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:20:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.73/8.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.73/8.74  
% 16.73/8.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.73/8.74  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 16.73/8.74  
% 16.73/8.74  %Foreground sorts:
% 16.73/8.74  
% 16.73/8.74  
% 16.73/8.74  %Background operators:
% 16.73/8.74  
% 16.73/8.74  
% 16.73/8.74  %Foreground operators:
% 16.73/8.74  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 16.73/8.74  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 16.73/8.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.73/8.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.73/8.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.73/8.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.73/8.74  tff('#skF_2', type, '#skF_2': $i).
% 16.73/8.74  tff('#skF_3', type, '#skF_3': $i).
% 16.73/8.74  tff('#skF_1', type, '#skF_1': $i).
% 16.73/8.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.73/8.74  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 16.73/8.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.73/8.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.73/8.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.73/8.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.73/8.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.73/8.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.73/8.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.73/8.74  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.73/8.74  
% 16.73/8.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.73/8.76  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 16.73/8.76  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.73/8.76  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.73/8.76  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 16.73/8.76  tff(f_57, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 16.73/8.76  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 16.73/8.76  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 16.73/8.76  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 16.73/8.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.73/8.76  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_124, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, C_52)=k3_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.73/8.76  tff(c_133, plain, (![B_51]: (k9_subset_1(u1_struct_0('#skF_1'), B_51, '#skF_3')=k3_xboole_0(B_51, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_124])).
% 16.73/8.76  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_134, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_22])).
% 16.73/8.76  tff(c_135, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_134])).
% 16.73/8.76  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_87, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.73/8.76  tff(c_94, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_87])).
% 16.73/8.76  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 16.73/8.76  tff(c_175, plain, (![B_58, A_59]: (v4_pre_topc(B_58, A_59) | ~v2_compts_1(B_58, A_59) | ~v8_pre_topc(A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_70])).
% 16.73/8.76  tff(c_182, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_175])).
% 16.73/8.76  tff(c_189, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_182])).
% 16.73/8.76  tff(c_185, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_175])).
% 16.73/8.76  tff(c_192, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_185])).
% 16.73/8.76  tff(c_208, plain, (![B_63, C_64, A_65]: (v4_pre_topc(k3_xboole_0(B_63, C_64), A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~v4_pre_topc(C_64, A_65) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_65))) | ~v4_pre_topc(B_63, A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.73/8.76  tff(c_215, plain, (![B_63]: (v4_pre_topc(k3_xboole_0(B_63, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_63, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_208])).
% 16.73/8.76  tff(c_553, plain, (![B_84]: (v4_pre_topc(k3_xboole_0(B_84, '#skF_3'), '#skF_1') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_84, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_192, c_215])).
% 16.73/8.76  tff(c_560, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_553])).
% 16.73/8.76  tff(c_567, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2, c_560])).
% 16.73/8.76  tff(c_110, plain, (![A_44, C_45, B_46]: (r1_tarski(k3_xboole_0(A_44, C_45), B_46) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.73/8.76  tff(c_113, plain, (![B_2, A_1, B_46]: (r1_tarski(k3_xboole_0(B_2, A_1), B_46) | ~r1_tarski(A_1, B_46))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 16.73/8.76  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.73/8.76  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.73/8.76  tff(c_475, plain, (![C_78, A_79, B_80]: (v2_compts_1(C_78, A_79) | ~v4_pre_topc(C_78, A_79) | ~r1_tarski(C_78, B_80) | ~v2_compts_1(B_80, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.73/8.76  tff(c_1483, plain, (![A_116, B_117, A_118]: (v2_compts_1(k3_xboole_0(A_116, B_117), A_118) | ~v4_pre_topc(k3_xboole_0(A_116, B_117), A_118) | ~v2_compts_1(A_116, A_118) | ~m1_subset_1(k3_xboole_0(A_116, B_117), k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(A_116, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(resolution, [status(thm)], [c_6, c_475])).
% 16.73/8.76  tff(c_4432, plain, (![A_201, B_202, A_203]: (v2_compts_1(k3_xboole_0(A_201, B_202), A_203) | ~v4_pre_topc(k3_xboole_0(A_201, B_202), A_203) | ~v2_compts_1(A_201, A_203) | ~m1_subset_1(A_201, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | ~r1_tarski(k3_xboole_0(A_201, B_202), u1_struct_0(A_203)))), inference(resolution, [status(thm)], [c_14, c_1483])).
% 16.73/8.76  tff(c_22673, plain, (![B_303, A_304, A_305]: (v2_compts_1(k3_xboole_0(B_303, A_304), A_305) | ~v4_pre_topc(k3_xboole_0(B_303, A_304), A_305) | ~v2_compts_1(B_303, A_305) | ~m1_subset_1(B_303, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | ~r1_tarski(A_304, u1_struct_0(A_305)))), inference(resolution, [status(thm)], [c_113, c_4432])).
% 16.73/8.76  tff(c_22777, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_567, c_22673])).
% 16.73/8.76  tff(c_22839, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_34, c_30, c_24, c_22777])).
% 16.73/8.76  tff(c_22841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_22839])).
% 16.73/8.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.73/8.76  
% 16.73/8.76  Inference rules
% 16.73/8.76  ----------------------
% 16.73/8.76  #Ref     : 0
% 16.73/8.76  #Sup     : 6534
% 16.73/8.76  #Fact    : 0
% 16.73/8.76  #Define  : 0
% 16.73/8.76  #Split   : 4
% 16.73/8.76  #Chain   : 0
% 16.73/8.76  #Close   : 0
% 16.73/8.76  
% 16.73/8.76  Ordering : KBO
% 16.73/8.76  
% 16.73/8.76  Simplification rules
% 16.73/8.76  ----------------------
% 16.73/8.76  #Subsume      : 862
% 16.73/8.76  #Demod        : 914
% 16.73/8.76  #Tautology    : 774
% 16.73/8.76  #SimpNegUnit  : 5
% 16.73/8.76  #BackRed      : 1
% 16.73/8.76  
% 16.73/8.76  #Partial instantiations: 0
% 16.73/8.76  #Strategies tried      : 1
% 16.73/8.76  
% 16.73/8.76  Timing (in seconds)
% 16.73/8.76  ----------------------
% 16.73/8.76  Preprocessing        : 0.34
% 16.73/8.76  Parsing              : 0.18
% 16.73/8.76  CNF conversion       : 0.02
% 16.73/8.76  Main loop            : 7.61
% 16.73/8.76  Inferencing          : 1.20
% 16.73/8.76  Reduction            : 5.22
% 16.73/8.76  Demodulation         : 5.03
% 16.73/8.76  BG Simplification    : 0.21
% 16.73/8.76  Subsumption          : 0.77
% 16.73/8.76  Abstraction          : 0.24
% 16.73/8.76  MUC search           : 0.00
% 16.73/8.76  Cooper               : 0.00
% 16.73/8.76  Total                : 7.98
% 16.73/8.76  Index Insertion      : 0.00
% 16.73/8.76  Index Deletion       : 0.00
% 16.73/8.76  Index Matching       : 0.00
% 16.73/8.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
