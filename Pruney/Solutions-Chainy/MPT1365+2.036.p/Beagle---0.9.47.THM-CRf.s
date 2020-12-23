%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:59 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 100 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 326 expanded)
%              Number of equality atoms :    3 (   3 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_69,plain,(
    ! [A_41,B_42,C_43] :
      ( k9_subset_1(A_41,B_42,C_43) = k3_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_3') = k3_xboole_0(B_42,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_20,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_111,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_154,plain,(
    ! [B_61,A_62] :
      ( v4_pre_topc(B_61,A_62)
      | ~ v2_compts_1(B_61,A_62)
      | ~ v8_pre_topc(A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_161,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_154])).

tff(c_168,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_24,c_161])).

tff(c_22,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_164,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_154])).

tff(c_171,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_22,c_164])).

tff(c_309,plain,(
    ! [B_80,C_81,A_82] :
      ( v4_pre_topc(k3_xboole_0(B_80,C_81),A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v4_pre_topc(C_81,A_82)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v4_pre_topc(B_80,A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_316,plain,(
    ! [B_80] :
      ( v4_pre_topc(k3_xboole_0(B_80,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_80,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_309])).

tff(c_539,plain,(
    ! [B_112] :
      ( v4_pre_topc(k3_xboole_0(B_112,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_112,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_171,c_316])).

tff(c_546,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_539])).

tff(c_553,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_546])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_36])).

tff(c_59,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_43,c_59])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_438,plain,(
    ! [C_98,A_99,B_100] :
      ( v2_compts_1(C_98,A_99)
      | ~ v4_pre_topc(C_98,A_99)
      | ~ r1_tarski(C_98,B_100)
      | ~ v2_compts_1(B_100,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_880,plain,(
    ! [A_166,B_167,A_168] :
      ( v2_compts_1(k3_xboole_0(A_166,B_167),A_168)
      | ~ v4_pre_topc(k3_xboole_0(A_166,B_167),A_168)
      | ~ v2_compts_1(A_166,A_168)
      | ~ m1_subset_1(k3_xboole_0(A_166,B_167),k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(A_166,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_2,c_438])).

tff(c_1338,plain,(
    ! [A_239,B_240,A_241] :
      ( v2_compts_1(k3_xboole_0(A_239,B_240),A_241)
      | ~ v4_pre_topc(k3_xboole_0(A_239,B_240),A_241)
      | ~ v2_compts_1(A_239,A_241)
      | ~ m1_subset_1(A_239,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | ~ r1_tarski(k3_xboole_0(A_239,B_240),u1_struct_0(A_241)) ) ),
    inference(resolution,[status(thm)],[c_12,c_880])).

tff(c_1396,plain,(
    ! [A_239,B_240] :
      ( v2_compts_1(k3_xboole_0(A_239,B_240),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_239,B_240),'#skF_1')
      | ~ v2_compts_1(A_239,'#skF_1')
      | ~ m1_subset_1(A_239,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_239,B_240),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67,c_1338])).

tff(c_2000,plain,(
    ! [A_307,B_308] :
      ( v2_compts_1(k3_xboole_0(A_307,B_308),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_307,B_308),'#skF_1')
      | ~ v2_compts_1(A_307,'#skF_1')
      | ~ m1_subset_1(A_307,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_307,B_308),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1396])).

tff(c_2033,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_553,c_2000])).

tff(c_2067,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30,c_24,c_2033])).

tff(c_2069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_2067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:21:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.80  
% 4.52/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.80  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.52/1.80  
% 4.52/1.80  %Foreground sorts:
% 4.52/1.80  
% 4.52/1.80  
% 4.52/1.80  %Background operators:
% 4.52/1.80  
% 4.52/1.80  
% 4.52/1.80  %Foreground operators:
% 4.52/1.80  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.52/1.80  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.52/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.52/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.52/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.52/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.52/1.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.52/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.52/1.80  
% 4.52/1.81  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 4.52/1.81  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.52/1.81  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.52/1.81  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.52/1.81  tff(f_57, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 4.52/1.81  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.52/1.81  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.52/1.81  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 4.52/1.81  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_69, plain, (![A_41, B_42, C_43]: (k9_subset_1(A_41, B_42, C_43)=k3_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.52/1.81  tff(c_78, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_3')=k3_xboole_0(B_42, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_69])).
% 4.52/1.81  tff(c_20, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_111, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20])).
% 4.52/1.81  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.81  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_24, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_26, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_154, plain, (![B_61, A_62]: (v4_pre_topc(B_61, A_62) | ~v2_compts_1(B_61, A_62) | ~v8_pre_topc(A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.52/1.81  tff(c_161, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_154])).
% 4.52/1.81  tff(c_168, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_24, c_161])).
% 4.52/1.81  tff(c_22, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.52/1.81  tff(c_164, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_154])).
% 4.52/1.81  tff(c_171, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_22, c_164])).
% 4.52/1.81  tff(c_309, plain, (![B_80, C_81, A_82]: (v4_pre_topc(k3_xboole_0(B_80, C_81), A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~v4_pre_topc(C_81, A_82) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_82))) | ~v4_pre_topc(B_80, A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.52/1.81  tff(c_316, plain, (![B_80]: (v4_pre_topc(k3_xboole_0(B_80, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_80, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_309])).
% 4.52/1.81  tff(c_539, plain, (![B_112]: (v4_pre_topc(k3_xboole_0(B_112, '#skF_3'), '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_112, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_171, c_316])).
% 4.52/1.81  tff(c_546, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_539])).
% 4.52/1.81  tff(c_553, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_546])).
% 4.52/1.81  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.81  tff(c_43, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_36])).
% 4.52/1.81  tff(c_59, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.81  tff(c_67, plain, (![A_38]: (r1_tarski(A_38, u1_struct_0('#skF_1')) | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_43, c_59])).
% 4.52/1.81  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.52/1.81  tff(c_438, plain, (![C_98, A_99, B_100]: (v2_compts_1(C_98, A_99) | ~v4_pre_topc(C_98, A_99) | ~r1_tarski(C_98, B_100) | ~v2_compts_1(B_100, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.52/1.81  tff(c_880, plain, (![A_166, B_167, A_168]: (v2_compts_1(k3_xboole_0(A_166, B_167), A_168) | ~v4_pre_topc(k3_xboole_0(A_166, B_167), A_168) | ~v2_compts_1(A_166, A_168) | ~m1_subset_1(k3_xboole_0(A_166, B_167), k1_zfmisc_1(u1_struct_0(A_168))) | ~m1_subset_1(A_166, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168))), inference(resolution, [status(thm)], [c_2, c_438])).
% 4.52/1.81  tff(c_1338, plain, (![A_239, B_240, A_241]: (v2_compts_1(k3_xboole_0(A_239, B_240), A_241) | ~v4_pre_topc(k3_xboole_0(A_239, B_240), A_241) | ~v2_compts_1(A_239, A_241) | ~m1_subset_1(A_239, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | ~r1_tarski(k3_xboole_0(A_239, B_240), u1_struct_0(A_241)))), inference(resolution, [status(thm)], [c_12, c_880])).
% 4.52/1.81  tff(c_1396, plain, (![A_239, B_240]: (v2_compts_1(k3_xboole_0(A_239, B_240), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_239, B_240), '#skF_1') | ~v2_compts_1(A_239, '#skF_1') | ~m1_subset_1(A_239, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_239, B_240), '#skF_2'))), inference(resolution, [status(thm)], [c_67, c_1338])).
% 4.52/1.81  tff(c_2000, plain, (![A_307, B_308]: (v2_compts_1(k3_xboole_0(A_307, B_308), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_307, B_308), '#skF_1') | ~v2_compts_1(A_307, '#skF_1') | ~m1_subset_1(A_307, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_307, B_308), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1396])).
% 4.52/1.81  tff(c_2033, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_553, c_2000])).
% 4.52/1.81  tff(c_2067, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30, c_24, c_2033])).
% 4.52/1.81  tff(c_2069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_2067])).
% 4.52/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.81  
% 4.52/1.81  Inference rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Ref     : 0
% 4.52/1.81  #Sup     : 441
% 4.52/1.81  #Fact    : 0
% 4.52/1.81  #Define  : 0
% 4.52/1.81  #Split   : 1
% 4.52/1.81  #Chain   : 0
% 4.52/1.81  #Close   : 0
% 4.52/1.81  
% 4.52/1.81  Ordering : KBO
% 4.52/1.81  
% 4.52/1.81  Simplification rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Subsume      : 54
% 4.52/1.81  #Demod        : 207
% 4.52/1.81  #Tautology    : 144
% 4.52/1.81  #SimpNegUnit  : 2
% 4.52/1.81  #BackRed      : 1
% 4.52/1.81  
% 4.52/1.81  #Partial instantiations: 0
% 4.52/1.81  #Strategies tried      : 1
% 4.52/1.81  
% 4.52/1.81  Timing (in seconds)
% 4.52/1.81  ----------------------
% 4.52/1.81  Preprocessing        : 0.31
% 4.52/1.81  Parsing              : 0.17
% 4.52/1.81  CNF conversion       : 0.02
% 4.52/1.81  Main loop            : 0.71
% 4.52/1.81  Inferencing          : 0.25
% 4.52/1.81  Reduction            : 0.20
% 4.52/1.82  Demodulation         : 0.15
% 4.52/1.82  BG Simplification    : 0.03
% 4.52/1.82  Subsumption          : 0.17
% 4.52/1.82  Abstraction          : 0.04
% 4.52/1.82  MUC search           : 0.00
% 4.52/1.82  Cooper               : 0.00
% 4.52/1.82  Total                : 1.04
% 4.52/1.82  Index Insertion      : 0.00
% 4.52/1.82  Index Deletion       : 0.00
% 4.52/1.82  Index Matching       : 0.00
% 4.52/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
