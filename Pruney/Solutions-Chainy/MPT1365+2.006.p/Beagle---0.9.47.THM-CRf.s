%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 120 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 346 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_105,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_86,axiom,(
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

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_156,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_165,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_207,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_18])).

tff(c_208,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_207])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_223,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(B_56,A_57)
      | ~ v2_compts_1(B_56,A_57)
      | ~ v8_pre_topc(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_239,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_252,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_239])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_236,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_249,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_236])).

tff(c_164,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_2') = k3_xboole_0(B_50,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_156])).

tff(c_450,plain,(
    ! [A_76,B_77,C_78] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_76),B_77,C_78),A_76)
      | ~ v4_pre_topc(C_78,A_76)
      | ~ v4_pre_topc(B_77,A_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_459,plain,(
    ! [B_50] :
      ( v4_pre_topc(k3_xboole_0(B_50,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_50,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_450])).

tff(c_498,plain,(
    ! [B_81] :
      ( v4_pre_topc(k3_xboole_0(B_81,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_249,c_459])).

tff(c_532,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_498])).

tff(c_556,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_532])).

tff(c_209,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_1'),B_55,'#skF_3') = k3_xboole_0(B_55,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    ! [B_55] :
      ( m1_subset_1(k3_xboole_0(B_55,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_6])).

tff(c_253,plain,(
    ! [B_58] : m1_subset_1(k3_xboole_0(B_58,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_215])).

tff(c_262,plain,(
    ! [A_41] : m1_subset_1(k3_xboole_0('#skF_3',A_41),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_253])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_328,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_compts_1(C_64,A_65)
      | ~ v4_pre_topc(C_64,A_65)
      | ~ r1_tarski(C_64,B_66)
      | ~ v2_compts_1(B_66,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_893,plain,(
    ! [A_106,B_107,A_108] :
      ( v2_compts_1(k3_xboole_0(A_106,B_107),A_108)
      | ~ v4_pre_topc(k3_xboole_0(A_106,B_107),A_108)
      | ~ v2_compts_1(A_106,A_108)
      | ~ m1_subset_1(k3_xboole_0(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(A_106,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_2,c_328])).

tff(c_920,plain,(
    ! [A_41] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_41),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_41),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_262,c_893])).

tff(c_972,plain,(
    ! [A_109] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_109),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_109),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_20,c_920])).

tff(c_986,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_556,c_972])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.25/1.51  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.25/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.25/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.25/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.25/1.51  
% 3.25/1.52  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.25/1.52  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.25/1.52  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.25/1.52  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.25/1.52  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.25/1.52  tff(f_55, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 3.25/1.52  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.25/1.52  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.25/1.52  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.25/1.52  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.52  tff(c_67, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.52  tff(c_82, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_4, c_67])).
% 3.25/1.52  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.52  tff(c_88, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 3.25/1.52  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_156, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.52  tff(c_165, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_156])).
% 3.25/1.52  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_207, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_18])).
% 3.25/1.52  tff(c_208, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_207])).
% 3.25/1.52  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_223, plain, (![B_56, A_57]: (v4_pre_topc(B_56, A_57) | ~v2_compts_1(B_56, A_57) | ~v8_pre_topc(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.25/1.52  tff(c_239, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_223])).
% 3.25/1.52  tff(c_252, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_239])).
% 3.25/1.52  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.25/1.52  tff(c_236, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_223])).
% 3.25/1.52  tff(c_249, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_236])).
% 3.25/1.52  tff(c_164, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_2')=k3_xboole_0(B_50, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_156])).
% 3.25/1.52  tff(c_450, plain, (![A_76, B_77, C_78]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_76), B_77, C_78), A_76) | ~v4_pre_topc(C_78, A_76) | ~v4_pre_topc(B_77, A_76) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.25/1.52  tff(c_459, plain, (![B_50]: (v4_pre_topc(k3_xboole_0(B_50, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_50, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_450])).
% 3.25/1.52  tff(c_498, plain, (![B_81]: (v4_pre_topc(k3_xboole_0(B_81, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_249, c_459])).
% 3.25/1.52  tff(c_532, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_498])).
% 3.25/1.52  tff(c_556, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_532])).
% 3.25/1.52  tff(c_209, plain, (![B_55]: (k9_subset_1(u1_struct_0('#skF_1'), B_55, '#skF_3')=k3_xboole_0(B_55, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_156])).
% 3.25/1.52  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.52  tff(c_215, plain, (![B_55]: (m1_subset_1(k3_xboole_0(B_55, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_209, c_6])).
% 3.25/1.52  tff(c_253, plain, (![B_58]: (m1_subset_1(k3_xboole_0(B_58, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_215])).
% 3.25/1.52  tff(c_262, plain, (![A_41]: (m1_subset_1(k3_xboole_0('#skF_3', A_41), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_253])).
% 3.25/1.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.52  tff(c_328, plain, (![C_64, A_65, B_66]: (v2_compts_1(C_64, A_65) | ~v4_pre_topc(C_64, A_65) | ~r1_tarski(C_64, B_66) | ~v2_compts_1(B_66, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.52  tff(c_893, plain, (![A_106, B_107, A_108]: (v2_compts_1(k3_xboole_0(A_106, B_107), A_108) | ~v4_pre_topc(k3_xboole_0(A_106, B_107), A_108) | ~v2_compts_1(A_106, A_108) | ~m1_subset_1(k3_xboole_0(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(A_106, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(resolution, [status(thm)], [c_2, c_328])).
% 3.25/1.52  tff(c_920, plain, (![A_41]: (v2_compts_1(k3_xboole_0('#skF_3', A_41), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_41), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_262, c_893])).
% 3.25/1.52  tff(c_972, plain, (![A_109]: (v2_compts_1(k3_xboole_0('#skF_3', A_109), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_109), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_20, c_920])).
% 3.25/1.52  tff(c_986, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_556, c_972])).
% 3.25/1.52  tff(c_1014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_986])).
% 3.25/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.52  
% 3.25/1.52  Inference rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Ref     : 0
% 3.25/1.52  #Sup     : 210
% 3.25/1.52  #Fact    : 0
% 3.25/1.52  #Define  : 0
% 3.25/1.52  #Split   : 0
% 3.25/1.52  #Chain   : 0
% 3.25/1.52  #Close   : 0
% 3.25/1.52  
% 3.25/1.52  Ordering : KBO
% 3.25/1.52  
% 3.25/1.52  Simplification rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Subsume      : 16
% 3.25/1.52  #Demod        : 193
% 3.25/1.52  #Tautology    : 80
% 3.25/1.52  #SimpNegUnit  : 2
% 3.25/1.52  #BackRed      : 1
% 3.25/1.52  
% 3.25/1.52  #Partial instantiations: 0
% 3.25/1.52  #Strategies tried      : 1
% 3.25/1.52  
% 3.25/1.52  Timing (in seconds)
% 3.25/1.52  ----------------------
% 3.25/1.53  Preprocessing        : 0.32
% 3.25/1.53  Parsing              : 0.17
% 3.25/1.53  CNF conversion       : 0.02
% 3.25/1.53  Main loop            : 0.44
% 3.25/1.53  Inferencing          : 0.15
% 3.25/1.53  Reduction            : 0.18
% 3.25/1.53  Demodulation         : 0.15
% 3.25/1.53  BG Simplification    : 0.02
% 3.25/1.53  Subsumption          : 0.06
% 3.25/1.53  Abstraction          : 0.02
% 3.25/1.53  MUC search           : 0.00
% 3.25/1.53  Cooper               : 0.00
% 3.25/1.53  Total                : 0.80
% 3.25/1.53  Index Insertion      : 0.00
% 3.25/1.53  Index Deletion       : 0.00
% 3.25/1.53  Index Matching       : 0.00
% 3.25/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
