%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 172 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 510 expanded)
%              Number of equality atoms :   10 (  53 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    ! [A_42,B_43,C_44] :
      ( k9_subset_1(A_42,B_43,C_44) = k3_xboole_0(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_1'),B_43,'#skF_2') = k3_xboole_0(B_43,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_87,plain,(
    ! [A_48,C_49,B_50] :
      ( k9_subset_1(A_48,C_49,B_50) = k9_subset_1(A_48,B_50,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_50) ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_109,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_52) = k3_xboole_0(B_52,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_53,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_1'),B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_116,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_53])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_72,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_140,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_72])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_219,plain,(
    ! [B_56,A_57] :
      ( v4_pre_topc(B_56,A_57)
      | ~ v2_compts_1(B_56,A_57)
      | ~ v8_pre_topc(A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_232,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_219])).

tff(c_245,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_232])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_235,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_248,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_235])).

tff(c_464,plain,(
    ! [A_70,B_71,C_72] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_70),B_71,C_72),A_70)
      | ~ v4_pre_topc(C_72,A_70)
      | ~ v4_pre_topc(B_71,A_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_476,plain,(
    ! [B_43] :
      ( v4_pre_topc(k3_xboole_0(B_43,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_43,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_464])).

tff(c_523,plain,(
    ! [B_76] :
      ( v4_pre_topc(k3_xboole_0(B_76,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_76,'#skF_1')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_248,c_476])).

tff(c_548,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_562,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_116,c_548])).

tff(c_73,plain,(
    ! [B_47] : k9_subset_1(u1_struct_0('#skF_1'),B_47,'#skF_3') = k3_xboole_0(B_47,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [B_47] :
      ( m1_subset_1(k3_xboole_0(B_47,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_6])).

tff(c_85,plain,(
    ! [B_47] : m1_subset_1(k3_xboole_0(B_47,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_79])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [C_65,A_66,B_67] :
      ( v2_compts_1(C_65,A_66)
      | ~ v4_pre_topc(C_65,A_66)
      | ~ r1_tarski(C_65,B_67)
      | ~ v2_compts_1(B_67,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1299,plain,(
    ! [A_117,B_118,A_119] :
      ( v2_compts_1(k3_xboole_0(A_117,B_118),A_119)
      | ~ v4_pre_topc(k3_xboole_0(A_117,B_118),A_119)
      | ~ v2_compts_1(A_117,A_119)
      | ~ m1_subset_1(k3_xboole_0(A_117,B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(A_117,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_2,c_315])).

tff(c_1341,plain,(
    ! [B_47] :
      ( v2_compts_1(k3_xboole_0(B_47,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_47,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_47,'#skF_1')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_85,c_1299])).

tff(c_5139,plain,(
    ! [B_248] :
      ( v2_compts_1(k3_xboole_0(B_248,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_248,'#skF_3'),'#skF_1')
      | ~ v2_compts_1(B_248,'#skF_1')
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1341])).

tff(c_5188,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_5139])).

tff(c_5213,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_562,c_116,c_116,c_5188])).

tff(c_5215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_5213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.47  
% 7.10/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.48  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 7.10/2.48  
% 7.10/2.48  %Foreground sorts:
% 7.10/2.48  
% 7.10/2.48  
% 7.10/2.48  %Background operators:
% 7.10/2.48  
% 7.10/2.48  
% 7.10/2.48  %Foreground operators:
% 7.10/2.48  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 7.10/2.48  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 7.10/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.10/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.10/2.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.10/2.48  tff('#skF_2', type, '#skF_2': $i).
% 7.10/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.10/2.48  tff('#skF_1', type, '#skF_1': $i).
% 7.10/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.10/2.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.10/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.10/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.10/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.10/2.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.10/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.10/2.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.10/2.48  
% 7.10/2.49  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 7.10/2.49  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.10/2.49  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 7.10/2.49  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 7.10/2.49  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 7.10/2.49  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.10/2.49  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.10/2.49  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 7.10/2.49  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_44, plain, (![A_42, B_43, C_44]: (k9_subset_1(A_42, B_43, C_44)=k3_xboole_0(B_43, C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.10/2.49  tff(c_52, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_1'), B_43, '#skF_2')=k3_xboole_0(B_43, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_44])).
% 7.10/2.49  tff(c_87, plain, (![A_48, C_49, B_50]: (k9_subset_1(A_48, C_49, B_50)=k9_subset_1(A_48, B_50, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.10/2.49  tff(c_93, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_50))), inference(resolution, [status(thm)], [c_28, c_87])).
% 7.10/2.49  tff(c_109, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_52)=k3_xboole_0(B_52, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93])).
% 7.10/2.49  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_53, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_1'), B_43, '#skF_3')=k3_xboole_0(B_43, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_44])).
% 7.10/2.49  tff(c_116, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_53])).
% 7.10/2.49  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_72, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18])).
% 7.10/2.49  tff(c_140, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_72])).
% 7.10/2.49  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_219, plain, (![B_56, A_57]: (v4_pre_topc(B_56, A_57) | ~v2_compts_1(B_56, A_57) | ~v8_pre_topc(A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.10/2.49  tff(c_232, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_219])).
% 7.10/2.49  tff(c_245, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_232])).
% 7.10/2.49  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.10/2.49  tff(c_235, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_219])).
% 7.10/2.49  tff(c_248, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_235])).
% 7.10/2.49  tff(c_464, plain, (![A_70, B_71, C_72]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_70), B_71, C_72), A_70) | ~v4_pre_topc(C_72, A_70) | ~v4_pre_topc(B_71, A_70) | ~m1_subset_1(C_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.10/2.49  tff(c_476, plain, (![B_43]: (v4_pre_topc(k3_xboole_0(B_43, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_43, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_464])).
% 7.10/2.49  tff(c_523, plain, (![B_76]: (v4_pre_topc(k3_xboole_0(B_76, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_76, '#skF_1') | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_248, c_476])).
% 7.10/2.49  tff(c_548, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_523])).
% 7.10/2.49  tff(c_562, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_116, c_548])).
% 7.10/2.49  tff(c_73, plain, (![B_47]: (k9_subset_1(u1_struct_0('#skF_1'), B_47, '#skF_3')=k3_xboole_0(B_47, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_44])).
% 7.10/2.49  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.10/2.49  tff(c_79, plain, (![B_47]: (m1_subset_1(k3_xboole_0(B_47, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_73, c_6])).
% 7.10/2.49  tff(c_85, plain, (![B_47]: (m1_subset_1(k3_xboole_0(B_47, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_79])).
% 7.10/2.49  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.10/2.49  tff(c_315, plain, (![C_65, A_66, B_67]: (v2_compts_1(C_65, A_66) | ~v4_pre_topc(C_65, A_66) | ~r1_tarski(C_65, B_67) | ~v2_compts_1(B_67, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.10/2.49  tff(c_1299, plain, (![A_117, B_118, A_119]: (v2_compts_1(k3_xboole_0(A_117, B_118), A_119) | ~v4_pre_topc(k3_xboole_0(A_117, B_118), A_119) | ~v2_compts_1(A_117, A_119) | ~m1_subset_1(k3_xboole_0(A_117, B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(A_117, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(resolution, [status(thm)], [c_2, c_315])).
% 7.10/2.49  tff(c_1341, plain, (![B_47]: (v2_compts_1(k3_xboole_0(B_47, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_47, '#skF_3'), '#skF_1') | ~v2_compts_1(B_47, '#skF_1') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_1299])).
% 7.10/2.49  tff(c_5139, plain, (![B_248]: (v2_compts_1(k3_xboole_0(B_248, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_248, '#skF_3'), '#skF_1') | ~v2_compts_1(B_248, '#skF_1') | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1341])).
% 7.10/2.49  tff(c_5188, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_5139])).
% 7.10/2.49  tff(c_5213, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_562, c_116, c_116, c_5188])).
% 7.10/2.49  tff(c_5215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_5213])).
% 7.10/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.10/2.49  
% 7.10/2.49  Inference rules
% 7.10/2.49  ----------------------
% 7.10/2.49  #Ref     : 0
% 7.10/2.49  #Sup     : 1328
% 7.10/2.49  #Fact    : 0
% 7.10/2.49  #Define  : 0
% 7.10/2.49  #Split   : 0
% 7.10/2.49  #Chain   : 0
% 7.10/2.49  #Close   : 0
% 7.10/2.49  
% 7.10/2.49  Ordering : KBO
% 7.10/2.49  
% 7.10/2.49  Simplification rules
% 7.10/2.49  ----------------------
% 7.10/2.49  #Subsume      : 24
% 7.10/2.49  #Demod        : 1058
% 7.10/2.49  #Tautology    : 296
% 7.10/2.49  #SimpNegUnit  : 1
% 7.10/2.49  #BackRed      : 2
% 7.10/2.49  
% 7.10/2.49  #Partial instantiations: 0
% 7.10/2.49  #Strategies tried      : 1
% 7.10/2.49  
% 7.10/2.49  Timing (in seconds)
% 7.10/2.49  ----------------------
% 7.10/2.50  Preprocessing        : 0.30
% 7.10/2.50  Parsing              : 0.16
% 7.10/2.50  CNF conversion       : 0.02
% 7.10/2.50  Main loop            : 1.42
% 7.10/2.50  Inferencing          : 0.41
% 7.10/2.50  Reduction            : 0.64
% 7.10/2.50  Demodulation         : 0.53
% 7.10/2.50  BG Simplification    : 0.06
% 7.10/2.50  Subsumption          : 0.21
% 7.10/2.50  Abstraction          : 0.09
% 7.10/2.50  MUC search           : 0.00
% 7.10/2.50  Cooper               : 0.00
% 7.10/2.50  Total                : 1.76
% 7.10/2.50  Index Insertion      : 0.00
% 7.10/2.50  Index Deletion       : 0.00
% 7.10/2.50  Index Matching       : 0.00
% 7.10/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
