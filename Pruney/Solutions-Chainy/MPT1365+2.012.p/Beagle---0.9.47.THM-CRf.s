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
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 108 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 334 expanded)
%              Number of equality atoms :    6 (  13 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

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

tff(f_29,axiom,(
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

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_92,plain,(
    ! [A_42,B_43,C_44] :
      ( k9_subset_1(A_42,B_43,C_44) = k3_xboole_0(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_1'),B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_99,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_18])).

tff(c_100,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

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

tff(c_209,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(B_56,A_57)
      | ~ v2_compts_1(B_56,A_57)
      | ~ v8_pre_topc(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_228,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_209])).

tff(c_247,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_228])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_231,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_209])).

tff(c_250,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_231])).

tff(c_98,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_1'),B_43,'#skF_2') = k3_xboole_0(B_43,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_519,plain,(
    ! [A_80,B_81,C_82] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_80),B_81,C_82),A_80)
      | ~ v4_pre_topc(C_82,A_80)
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_528,plain,(
    ! [B_43] :
      ( v4_pre_topc(k3_xboole_0(B_43,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_43,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_519])).

tff(c_543,plain,(
    ! [B_83] :
      ( v4_pre_topc(k3_xboole_0(B_83,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_83,'#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_250,c_528])).

tff(c_586,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_543])).

tff(c_618,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_586])).

tff(c_110,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1(k9_subset_1(A_46,B_47,C_48),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [B_43] :
      ( m1_subset_1(k3_xboole_0(B_43,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_110])).

tff(c_119,plain,(
    ! [B_49] : m1_subset_1(k3_xboole_0(B_49,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_115])).

tff(c_125,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_3',A_1),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_383,plain,(
    ! [C_68,A_69,B_70] :
      ( v2_compts_1(C_68,A_69)
      | ~ v4_pre_topc(C_68,A_69)
      | ~ r1_tarski(C_68,B_70)
      | ~ v2_compts_1(B_70,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_899,plain,(
    ! [A_106,B_107,A_108] :
      ( v2_compts_1(k3_xboole_0(A_106,B_107),A_108)
      | ~ v4_pre_topc(k3_xboole_0(A_106,B_107),A_108)
      | ~ v2_compts_1(A_106,A_108)
      | ~ m1_subset_1(k3_xboole_0(A_106,B_107),k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(A_106,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_4,c_383])).

tff(c_932,plain,(
    ! [A_1] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_125,c_899])).

tff(c_1035,plain,(
    ! [A_110] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_110),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_110),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_20,c_932])).

tff(c_1071,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_618,c_1035])).

tff(c_1100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:31:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.07  
% 4.24/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.08  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.24/2.08  
% 4.24/2.08  %Foreground sorts:
% 4.24/2.08  
% 4.24/2.08  
% 4.24/2.08  %Background operators:
% 4.24/2.08  
% 4.24/2.08  
% 4.24/2.08  %Foreground operators:
% 4.24/2.08  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.24/2.08  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.24/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.24/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.24/2.08  tff('#skF_2', type, '#skF_2': $i).
% 4.24/2.08  tff('#skF_3', type, '#skF_3': $i).
% 4.24/2.08  tff('#skF_1', type, '#skF_1': $i).
% 4.24/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.24/2.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.24/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.24/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.24/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.24/2.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.24/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.24/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.24/2.08  
% 4.33/2.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.33/2.10  tff(f_105, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 4.33/2.10  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.33/2.10  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 4.33/2.10  tff(f_55, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 4.33/2.10  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.33/2.10  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.33/2.10  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 4.33/2.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.33/2.10  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_92, plain, (![A_42, B_43, C_44]: (k9_subset_1(A_42, B_43, C_44)=k3_xboole_0(B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/2.10  tff(c_97, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_1'), B_43, '#skF_3')=k3_xboole_0(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_92])).
% 4.33/2.10  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_99, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_18])).
% 4.33/2.10  tff(c_100, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 4.33/2.10  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_209, plain, (![B_56, A_57]: (v4_pre_topc(B_56, A_57) | ~v2_compts_1(B_56, A_57) | ~v8_pre_topc(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.33/2.10  tff(c_228, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_209])).
% 4.33/2.10  tff(c_247, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_228])).
% 4.33/2.10  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.33/2.10  tff(c_231, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_209])).
% 4.33/2.10  tff(c_250, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_231])).
% 4.33/2.10  tff(c_98, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_1'), B_43, '#skF_2')=k3_xboole_0(B_43, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_92])).
% 4.33/2.10  tff(c_519, plain, (![A_80, B_81, C_82]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_80), B_81, C_82), A_80) | ~v4_pre_topc(C_82, A_80) | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.33/2.10  tff(c_528, plain, (![B_43]: (v4_pre_topc(k3_xboole_0(B_43, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_43, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_519])).
% 4.33/2.10  tff(c_543, plain, (![B_83]: (v4_pre_topc(k3_xboole_0(B_83, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_83, '#skF_1') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_250, c_528])).
% 4.33/2.10  tff(c_586, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_543])).
% 4.33/2.10  tff(c_618, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_586])).
% 4.33/2.10  tff(c_110, plain, (![A_46, B_47, C_48]: (m1_subset_1(k9_subset_1(A_46, B_47, C_48), k1_zfmisc_1(A_46)) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.33/2.10  tff(c_115, plain, (![B_43]: (m1_subset_1(k3_xboole_0(B_43, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_97, c_110])).
% 4.33/2.10  tff(c_119, plain, (![B_49]: (m1_subset_1(k3_xboole_0(B_49, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_115])).
% 4.33/2.10  tff(c_125, plain, (![A_1]: (m1_subset_1(k3_xboole_0('#skF_3', A_1), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 4.33/2.10  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/2.10  tff(c_383, plain, (![C_68, A_69, B_70]: (v2_compts_1(C_68, A_69) | ~v4_pre_topc(C_68, A_69) | ~r1_tarski(C_68, B_70) | ~v2_compts_1(B_70, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.33/2.10  tff(c_899, plain, (![A_106, B_107, A_108]: (v2_compts_1(k3_xboole_0(A_106, B_107), A_108) | ~v4_pre_topc(k3_xboole_0(A_106, B_107), A_108) | ~v2_compts_1(A_106, A_108) | ~m1_subset_1(k3_xboole_0(A_106, B_107), k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(A_106, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(resolution, [status(thm)], [c_4, c_383])).
% 4.33/2.10  tff(c_932, plain, (![A_1]: (v2_compts_1(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_125, c_899])).
% 4.33/2.10  tff(c_1035, plain, (![A_110]: (v2_compts_1(k3_xboole_0('#skF_3', A_110), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_110), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_20, c_932])).
% 4.33/2.10  tff(c_1071, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_618, c_1035])).
% 4.33/2.10  tff(c_1100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_1071])).
% 4.33/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/2.10  
% 4.33/2.10  Inference rules
% 4.33/2.10  ----------------------
% 4.33/2.10  #Ref     : 0
% 4.33/2.10  #Sup     : 225
% 4.33/2.10  #Fact    : 0
% 4.33/2.10  #Define  : 0
% 4.33/2.10  #Split   : 0
% 4.33/2.10  #Chain   : 0
% 4.33/2.10  #Close   : 0
% 4.33/2.10  
% 4.33/2.10  Ordering : KBO
% 4.33/2.10  
% 4.33/2.10  Simplification rules
% 4.33/2.10  ----------------------
% 4.33/2.10  #Subsume      : 22
% 4.33/2.10  #Demod        : 197
% 4.33/2.10  #Tautology    : 61
% 4.33/2.10  #SimpNegUnit  : 5
% 4.33/2.10  #BackRed      : 1
% 4.33/2.10  
% 4.33/2.10  #Partial instantiations: 0
% 4.33/2.10  #Strategies tried      : 1
% 4.33/2.10  
% 4.33/2.10  Timing (in seconds)
% 4.33/2.10  ----------------------
% 4.33/2.11  Preprocessing        : 0.49
% 4.33/2.11  Parsing              : 0.26
% 4.33/2.11  CNF conversion       : 0.03
% 4.33/2.11  Main loop            : 0.75
% 4.33/2.11  Inferencing          : 0.25
% 4.33/2.11  Reduction            : 0.31
% 4.33/2.11  Demodulation         : 0.25
% 4.33/2.11  BG Simplification    : 0.03
% 4.33/2.11  Subsumption          : 0.12
% 4.33/2.11  Abstraction          : 0.04
% 4.33/2.11  MUC search           : 0.00
% 4.33/2.11  Cooper               : 0.00
% 4.33/2.11  Total                : 1.30
% 4.33/2.11  Index Insertion      : 0.00
% 4.33/2.11  Index Deletion       : 0.00
% 4.33/2.11  Index Matching       : 0.00
% 4.33/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
