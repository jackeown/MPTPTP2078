%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:56 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :  111 (1167 expanded)
%              Number of leaves         :   26 ( 411 expanded)
%              Depth                    :   17
%              Number of atoms          :  219 (2736 expanded)
%              Number of equality atoms :   30 ( 424 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_111,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_61,axiom,(
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
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_92,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_100,plain,(
    ! [A_40,B_41,C_42] :
      ( k9_subset_1(A_40,B_41,C_42) = k3_xboole_0(B_41,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_41,'#skF_3') = k3_xboole_0(B_41,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_100])).

tff(c_24,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_110,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_24])).

tff(c_41,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_41])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_257,plain,(
    ! [B_59,A_60] :
      ( v4_pre_topc(B_59,A_60)
      | ~ v2_compts_1(B_59,A_60)
      | ~ v8_pre_topc(A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_274,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_257])).

tff(c_288,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_26,c_274])).

tff(c_28,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_277,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_257])).

tff(c_291,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_277])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_456,plain,(
    ! [B_75,C_76,A_77] :
      ( v4_pre_topc(k3_xboole_0(B_75,C_76),A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v4_pre_topc(C_76,A_77)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v4_pre_topc(B_75,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1619,plain,(
    ! [B_142,A_143,A_144] :
      ( v4_pre_topc(k3_xboole_0(B_142,A_143),A_144)
      | ~ v4_pre_topc(A_143,A_144)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v4_pre_topc(B_142,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | ~ r1_tarski(A_143,u1_struct_0(A_144)) ) ),
    inference(resolution,[status(thm)],[c_16,c_456])).

tff(c_1646,plain,(
    ! [A_143] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_143),'#skF_1')
      | ~ v4_pre_topc(A_143,'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_143,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_1619])).

tff(c_1676,plain,(
    ! [A_143] :
      ( v4_pre_topc(k3_xboole_0('#skF_2',A_143),'#skF_1')
      | ~ v4_pre_topc(A_143,'#skF_1')
      | ~ r1_tarski(A_143,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_291,c_1646])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ! [B_54,B_55,A_56] :
      ( k9_subset_1(B_54,B_55,A_56) = k3_xboole_0(B_55,A_56)
      | ~ r1_tarski(A_56,B_54) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_244,plain,(
    ! [B_2,B_55] : k9_subset_1(B_2,B_55,B_2) = k3_xboole_0(B_55,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_120,plain,(
    ! [A_44,B_45,C_46] :
      ( m1_subset_1(k9_subset_1(A_44,B_45,C_46),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_292,plain,(
    ! [A_61,B_62,C_63] :
      ( r1_tarski(k9_subset_1(A_61,B_62,C_63),A_61)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(resolution,[status(thm)],[c_120,c_14])).

tff(c_361,plain,(
    ! [B_68,B_69] :
      ( r1_tarski(k3_xboole_0(B_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_292])).

tff(c_107,plain,(
    ! [B_12,B_41,A_11] :
      ( k9_subset_1(B_12,B_41,A_11) = k3_xboole_0(B_41,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_2122,plain,(
    ! [B_177,B_178,B_179] :
      ( k9_subset_1(B_177,B_178,k3_xboole_0(B_179,B_177)) = k3_xboole_0(B_178,k3_xboole_0(B_179,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(B_177)) ) ),
    inference(resolution,[status(thm)],[c_361,c_107])).

tff(c_2125,plain,(
    ! [B_12,B_178,B_179] :
      ( k9_subset_1(B_12,B_178,k3_xboole_0(B_179,B_12)) = k3_xboole_0(B_178,k3_xboole_0(B_179,B_12))
      | ~ r1_tarski(B_12,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_2122])).

tff(c_2128,plain,(
    ! [B_12,B_178,B_179] : k9_subset_1(B_12,B_178,k3_xboole_0(B_179,B_12)) = k3_xboole_0(B_178,k3_xboole_0(B_179,B_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2125])).

tff(c_245,plain,(
    ! [B_57,B_58] : k9_subset_1(B_57,B_58,B_57) = k3_xboole_0(B_58,B_57) ),
    inference(resolution,[status(thm)],[c_6,c_227])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_251,plain,(
    ! [B_58,B_57] :
      ( m1_subset_1(k3_xboole_0(B_58,B_57),k1_zfmisc_1(B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(B_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_10])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1090,plain,(
    ! [A_111,B_112,C_113] :
      ( k3_xboole_0(k9_subset_1(A_111,B_112,C_113),A_111) = k9_subset_1(A_111,B_112,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_292,c_8])).

tff(c_1110,plain,(
    ! [B_57,B_112,B_58] :
      ( k3_xboole_0(k9_subset_1(B_57,B_112,k3_xboole_0(B_58,B_57)),B_57) = k9_subset_1(B_57,B_112,k3_xboole_0(B_58,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(B_57)) ) ),
    inference(resolution,[status(thm)],[c_251,c_1090])).

tff(c_7012,plain,(
    ! [B_377,B_378,B_379] :
      ( k3_xboole_0(k3_xboole_0(B_377,k3_xboole_0(B_378,B_379)),B_379) = k3_xboole_0(B_377,k3_xboole_0(B_378,B_379))
      | ~ m1_subset_1(B_379,k1_zfmisc_1(B_379)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2128,c_1110])).

tff(c_128,plain,(
    ! [B_41] :
      ( m1_subset_1(k3_xboole_0(B_41,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_120])).

tff(c_132,plain,(
    ! [B_41] : m1_subset_1(k3_xboole_0(B_41,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_128])).

tff(c_133,plain,(
    ! [B_47] : m1_subset_1(k3_xboole_0(B_47,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_128])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k9_subset_1(A_8,B_9,C_10) = k3_xboole_0(B_9,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_560,plain,(
    ! [B_83,B_84] : k9_subset_1(u1_struct_0('#skF_1'),B_83,k3_xboole_0(B_84,'#skF_3')) = k3_xboole_0(B_83,k3_xboole_0(B_84,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_133,c_12])).

tff(c_569,plain,(
    ! [B_83,B_84] :
      ( m1_subset_1(k3_xboole_0(B_83,k3_xboole_0(B_84,'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_xboole_0(B_84,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_10])).

tff(c_581,plain,(
    ! [B_83,B_84] : m1_subset_1(k3_xboole_0(B_83,k3_xboole_0(B_84,'#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_569])).

tff(c_130,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(k9_subset_1(A_44,B_45,C_46),A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_120,c_14])).

tff(c_566,plain,(
    ! [B_83,B_84] :
      ( r1_tarski(k3_xboole_0(B_83,k3_xboole_0(B_84,'#skF_3')),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k3_xboole_0(B_84,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_130])).

tff(c_584,plain,(
    ! [B_85,B_86] : r1_tarski(k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_566])).

tff(c_602,plain,(
    ! [B_85,B_86] : k3_xboole_0(k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3')),u1_struct_0('#skF_1')) = k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_584,c_8])).

tff(c_2130,plain,(
    ! [B_180,B_181,B_182] : k9_subset_1(B_180,B_181,k3_xboole_0(B_182,B_180)) = k3_xboole_0(B_181,k3_xboole_0(B_182,B_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2125])).

tff(c_2533,plain,(
    ! [B_198,B_199,B_200] :
      ( m1_subset_1(k3_xboole_0(B_198,k3_xboole_0(B_199,B_200)),k1_zfmisc_1(B_200))
      | ~ m1_subset_1(k3_xboole_0(B_199,B_200),k1_zfmisc_1(B_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2130,c_10])).

tff(c_2576,plain,(
    ! [B_198,B_85,B_86] :
      ( m1_subset_1(k3_xboole_0(B_198,k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3')),u1_struct_0('#skF_1')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_2533])).

tff(c_2616,plain,(
    ! [B_198,B_85,B_86] : m1_subset_1(k3_xboole_0(B_198,k3_xboole_0(B_85,k3_xboole_0(B_86,'#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_602,c_2576])).

tff(c_579,plain,(
    ! [B_83,B_84] : r1_tarski(k3_xboole_0(B_83,k3_xboole_0(B_84,'#skF_3')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_566])).

tff(c_143,plain,(
    ! [B_9,B_47] : k9_subset_1(u1_struct_0('#skF_1'),B_9,k3_xboole_0(B_47,'#skF_3')) = k3_xboole_0(B_9,k3_xboole_0(B_47,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_133,c_12])).

tff(c_1281,plain,(
    ! [A_117,B_118,B_119,C_120] :
      ( k9_subset_1(A_117,B_118,k9_subset_1(A_117,B_119,C_120)) = k3_xboole_0(B_118,k9_subset_1(A_117,B_119,C_120))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_1291,plain,(
    ! [B_118,B_119,B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_118,k9_subset_1(u1_struct_0('#skF_1'),B_119,k3_xboole_0(B_41,'#skF_3'))) = k3_xboole_0(B_118,k9_subset_1(u1_struct_0('#skF_1'),B_119,k3_xboole_0(B_41,'#skF_3'))) ),
    inference(resolution,[status(thm)],[c_132,c_1281])).

tff(c_1306,plain,(
    ! [B_118,B_119,B_41] : k9_subset_1(u1_struct_0('#skF_1'),B_118,k3_xboole_0(B_119,k3_xboole_0(B_41,'#skF_3'))) = k3_xboole_0(B_118,k3_xboole_0(B_119,k3_xboole_0(B_41,'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_1291])).

tff(c_3563,plain,(
    ! [B_250,B_251,B_252] : k9_subset_1(u1_struct_0('#skF_1'),B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3'))) = k3_xboole_0(B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_1291])).

tff(c_1117,plain,(
    ! [B_12,B_112,A_11] :
      ( k3_xboole_0(k9_subset_1(B_12,B_112,A_11),B_12) = k9_subset_1(B_12,B_112,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_1090])).

tff(c_3587,plain,(
    ! [B_250,B_251,B_252] :
      ( k3_xboole_0(k3_xboole_0(B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3'))),u1_struct_0('#skF_1')) = k9_subset_1(u1_struct_0('#skF_1'),B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3')))
      | ~ r1_tarski(k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3')),u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3563,c_1117])).

tff(c_3635,plain,(
    ! [B_250,B_251,B_252] : k3_xboole_0(k3_xboole_0(B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3'))),u1_struct_0('#skF_1')) = k3_xboole_0(B_250,k3_xboole_0(B_251,k3_xboole_0(B_252,'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_1306,c_3587])).

tff(c_4553,plain,(
    ! [B_304,B_305,B_306] : k3_xboole_0(k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_306,'#skF_3'))),u1_struct_0('#skF_1')) = k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_306,'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_1306,c_3587])).

tff(c_2200,plain,(
    ! [B_181,B_182,B_180] :
      ( r1_tarski(k3_xboole_0(B_181,k3_xboole_0(B_182,B_180)),B_180)
      | ~ m1_subset_1(k3_xboole_0(B_182,B_180),k1_zfmisc_1(B_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2130,c_130])).

tff(c_4565,plain,(
    ! [B_181,B_304,B_305,B_306] :
      ( r1_tarski(k3_xboole_0(B_181,k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_306,'#skF_3')))),u1_struct_0('#skF_1'))
      | ~ m1_subset_1(k3_xboole_0(k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_306,'#skF_3'))),u1_struct_0('#skF_1')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4553,c_2200])).

tff(c_4626,plain,(
    ! [B_181,B_304,B_305,B_306] : r1_tarski(k3_xboole_0(B_181,k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_306,'#skF_3')))),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2616,c_3635,c_4565])).

tff(c_7162,plain,(
    ! [B_378,B_305,B_377,B_304,B_181] :
      ( r1_tarski(k3_xboole_0(B_181,k3_xboole_0(B_304,k3_xboole_0(B_305,k3_xboole_0(B_377,k3_xboole_0(B_378,'#skF_3'))))),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7012,c_4626])).

tff(c_11756,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7162])).

tff(c_11759,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_11756])).

tff(c_11763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11759])).

tff(c_11765,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7162])).

tff(c_1122,plain,(
    ! [B_114,B_115,A_116] :
      ( k3_xboole_0(k9_subset_1(B_114,B_115,A_116),B_114) = k9_subset_1(B_114,B_115,A_116)
      | ~ r1_tarski(A_116,B_114) ) ),
    inference(resolution,[status(thm)],[c_16,c_1090])).

tff(c_1249,plain,(
    ! [B_115,A_116] :
      ( m1_subset_1(k9_subset_1('#skF_3',B_115,A_116),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_116,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_132])).

tff(c_639,plain,(
    ! [C_89,A_90,B_91] :
      ( v2_compts_1(C_89,A_90)
      | ~ v4_pre_topc(C_89,A_90)
      | ~ r1_tarski(C_89,B_91)
      | ~ v2_compts_1(B_91,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8315,plain,(
    ! [A_399,B_400,C_401,A_402] :
      ( v2_compts_1(k9_subset_1(A_399,B_400,C_401),A_402)
      | ~ v4_pre_topc(k9_subset_1(A_399,B_400,C_401),A_402)
      | ~ v2_compts_1(A_399,A_402)
      | ~ m1_subset_1(k9_subset_1(A_399,B_400,C_401),k1_zfmisc_1(u1_struct_0(A_402)))
      | ~ m1_subset_1(A_399,k1_zfmisc_1(u1_struct_0(A_402)))
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(A_399)) ) ),
    inference(resolution,[status(thm)],[c_130,c_639])).

tff(c_8352,plain,(
    ! [B_115,A_116] :
      ( v2_compts_1(k9_subset_1('#skF_3',B_115,A_116),'#skF_1')
      | ~ v4_pre_topc(k9_subset_1('#skF_3',B_115,A_116),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_subset_1(A_116,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_116,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1249,c_8315])).

tff(c_22672,plain,(
    ! [B_882,A_883] :
      ( v2_compts_1(k9_subset_1('#skF_3',B_882,A_883),'#skF_1')
      | ~ v4_pre_topc(k9_subset_1('#skF_3',B_882,A_883),'#skF_1')
      | ~ m1_subset_1(A_883,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_883,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_26,c_8352])).

tff(c_22699,plain,(
    ! [B_55] :
      ( v2_compts_1(k9_subset_1('#skF_3',B_55,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_55,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_22672])).

tff(c_22704,plain,(
    ! [B_884] :
      ( v2_compts_1(k3_xboole_0(B_884,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(B_884,'#skF_3'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11765,c_244,c_22699])).

tff(c_22793,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1676,c_22704])).

tff(c_22857,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_288,c_22793])).

tff(c_22859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_22857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.92/5.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/5.23  
% 11.92/5.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/5.23  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 11.92/5.23  
% 11.92/5.23  %Foreground sorts:
% 11.92/5.23  
% 11.92/5.23  
% 11.92/5.23  %Background operators:
% 11.92/5.23  
% 11.92/5.23  
% 11.92/5.23  %Foreground operators:
% 11.92/5.23  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 11.92/5.23  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 11.92/5.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.92/5.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.92/5.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.92/5.23  tff('#skF_2', type, '#skF_2': $i).
% 11.92/5.23  tff('#skF_3', type, '#skF_3': $i).
% 11.92/5.23  tff('#skF_1', type, '#skF_1': $i).
% 11.92/5.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.92/5.23  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.92/5.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.92/5.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.92/5.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.92/5.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.92/5.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.92/5.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.92/5.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.92/5.23  
% 12.06/5.25  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 12.06/5.25  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.06/5.25  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.06/5.25  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 12.06/5.25  tff(f_61, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 12.06/5.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.06/5.25  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 12.06/5.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.06/5.25  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 12.06/5.25  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_100, plain, (![A_40, B_41, C_42]: (k9_subset_1(A_40, B_41, C_42)=k3_xboole_0(B_41, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.06/5.25  tff(c_108, plain, (![B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_41, '#skF_3')=k3_xboole_0(B_41, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_100])).
% 12.06/5.25  tff(c_24, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_110, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_24])).
% 12.06/5.25  tff(c_41, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.06/5.25  tff(c_48, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_41])).
% 12.06/5.25  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_30, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_26, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_257, plain, (![B_59, A_60]: (v4_pre_topc(B_59, A_60) | ~v2_compts_1(B_59, A_60) | ~v8_pre_topc(A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.06/5.25  tff(c_274, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_257])).
% 12.06/5.25  tff(c_288, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_26, c_274])).
% 12.06/5.25  tff(c_28, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.06/5.25  tff(c_277, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_257])).
% 12.06/5.25  tff(c_291, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_277])).
% 12.06/5.25  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.06/5.25  tff(c_456, plain, (![B_75, C_76, A_77]: (v4_pre_topc(k3_xboole_0(B_75, C_76), A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~v4_pre_topc(C_76, A_77) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_77))) | ~v4_pre_topc(B_75, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.06/5.25  tff(c_1619, plain, (![B_142, A_143, A_144]: (v4_pre_topc(k3_xboole_0(B_142, A_143), A_144) | ~v4_pre_topc(A_143, A_144) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_144))) | ~v4_pre_topc(B_142, A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | ~r1_tarski(A_143, u1_struct_0(A_144)))), inference(resolution, [status(thm)], [c_16, c_456])).
% 12.06/5.25  tff(c_1646, plain, (![A_143]: (v4_pre_topc(k3_xboole_0('#skF_2', A_143), '#skF_1') | ~v4_pre_topc(A_143, '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_143, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_1619])).
% 12.06/5.25  tff(c_1676, plain, (![A_143]: (v4_pre_topc(k3_xboole_0('#skF_2', A_143), '#skF_1') | ~v4_pre_topc(A_143, '#skF_1') | ~r1_tarski(A_143, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_291, c_1646])).
% 12.06/5.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.06/5.25  tff(c_227, plain, (![B_54, B_55, A_56]: (k9_subset_1(B_54, B_55, A_56)=k3_xboole_0(B_55, A_56) | ~r1_tarski(A_56, B_54))), inference(resolution, [status(thm)], [c_16, c_100])).
% 12.06/5.25  tff(c_244, plain, (![B_2, B_55]: (k9_subset_1(B_2, B_55, B_2)=k3_xboole_0(B_55, B_2))), inference(resolution, [status(thm)], [c_6, c_227])).
% 12.06/5.25  tff(c_120, plain, (![A_44, B_45, C_46]: (m1_subset_1(k9_subset_1(A_44, B_45, C_46), k1_zfmisc_1(A_44)) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.06/5.25  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.06/5.25  tff(c_292, plain, (![A_61, B_62, C_63]: (r1_tarski(k9_subset_1(A_61, B_62, C_63), A_61) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(resolution, [status(thm)], [c_120, c_14])).
% 12.06/5.25  tff(c_361, plain, (![B_68, B_69]: (r1_tarski(k3_xboole_0(B_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(B_69)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_292])).
% 12.06/5.25  tff(c_107, plain, (![B_12, B_41, A_11]: (k9_subset_1(B_12, B_41, A_11)=k3_xboole_0(B_41, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_100])).
% 12.06/5.25  tff(c_2122, plain, (![B_177, B_178, B_179]: (k9_subset_1(B_177, B_178, k3_xboole_0(B_179, B_177))=k3_xboole_0(B_178, k3_xboole_0(B_179, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(B_177)))), inference(resolution, [status(thm)], [c_361, c_107])).
% 12.06/5.25  tff(c_2125, plain, (![B_12, B_178, B_179]: (k9_subset_1(B_12, B_178, k3_xboole_0(B_179, B_12))=k3_xboole_0(B_178, k3_xboole_0(B_179, B_12)) | ~r1_tarski(B_12, B_12))), inference(resolution, [status(thm)], [c_16, c_2122])).
% 12.06/5.25  tff(c_2128, plain, (![B_12, B_178, B_179]: (k9_subset_1(B_12, B_178, k3_xboole_0(B_179, B_12))=k3_xboole_0(B_178, k3_xboole_0(B_179, B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2125])).
% 12.06/5.25  tff(c_245, plain, (![B_57, B_58]: (k9_subset_1(B_57, B_58, B_57)=k3_xboole_0(B_58, B_57))), inference(resolution, [status(thm)], [c_6, c_227])).
% 12.06/5.25  tff(c_10, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.06/5.25  tff(c_251, plain, (![B_58, B_57]: (m1_subset_1(k3_xboole_0(B_58, B_57), k1_zfmisc_1(B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(B_57)))), inference(superposition, [status(thm), theory('equality')], [c_245, c_10])).
% 12.06/5.25  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.06/5.25  tff(c_1090, plain, (![A_111, B_112, C_113]: (k3_xboole_0(k9_subset_1(A_111, B_112, C_113), A_111)=k9_subset_1(A_111, B_112, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_292, c_8])).
% 12.06/5.25  tff(c_1110, plain, (![B_57, B_112, B_58]: (k3_xboole_0(k9_subset_1(B_57, B_112, k3_xboole_0(B_58, B_57)), B_57)=k9_subset_1(B_57, B_112, k3_xboole_0(B_58, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(B_57)))), inference(resolution, [status(thm)], [c_251, c_1090])).
% 12.06/5.25  tff(c_7012, plain, (![B_377, B_378, B_379]: (k3_xboole_0(k3_xboole_0(B_377, k3_xboole_0(B_378, B_379)), B_379)=k3_xboole_0(B_377, k3_xboole_0(B_378, B_379)) | ~m1_subset_1(B_379, k1_zfmisc_1(B_379)))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2128, c_1110])).
% 12.06/5.25  tff(c_128, plain, (![B_41]: (m1_subset_1(k3_xboole_0(B_41, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_108, c_120])).
% 12.06/5.25  tff(c_132, plain, (![B_41]: (m1_subset_1(k3_xboole_0(B_41, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_128])).
% 12.06/5.25  tff(c_133, plain, (![B_47]: (m1_subset_1(k3_xboole_0(B_47, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_128])).
% 12.06/5.25  tff(c_12, plain, (![A_8, B_9, C_10]: (k9_subset_1(A_8, B_9, C_10)=k3_xboole_0(B_9, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.06/5.25  tff(c_560, plain, (![B_83, B_84]: (k9_subset_1(u1_struct_0('#skF_1'), B_83, k3_xboole_0(B_84, '#skF_3'))=k3_xboole_0(B_83, k3_xboole_0(B_84, '#skF_3')))), inference(resolution, [status(thm)], [c_133, c_12])).
% 12.06/5.25  tff(c_569, plain, (![B_83, B_84]: (m1_subset_1(k3_xboole_0(B_83, k3_xboole_0(B_84, '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0(B_84, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_560, c_10])).
% 12.06/5.25  tff(c_581, plain, (![B_83, B_84]: (m1_subset_1(k3_xboole_0(B_83, k3_xboole_0(B_84, '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_569])).
% 12.06/5.25  tff(c_130, plain, (![A_44, B_45, C_46]: (r1_tarski(k9_subset_1(A_44, B_45, C_46), A_44) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_120, c_14])).
% 12.06/5.25  tff(c_566, plain, (![B_83, B_84]: (r1_tarski(k3_xboole_0(B_83, k3_xboole_0(B_84, '#skF_3')), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_xboole_0(B_84, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_560, c_130])).
% 12.06/5.25  tff(c_584, plain, (![B_85, B_86]: (r1_tarski(k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3')), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_566])).
% 12.06/5.25  tff(c_602, plain, (![B_85, B_86]: (k3_xboole_0(k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3')), u1_struct_0('#skF_1'))=k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3')))), inference(resolution, [status(thm)], [c_584, c_8])).
% 12.06/5.25  tff(c_2130, plain, (![B_180, B_181, B_182]: (k9_subset_1(B_180, B_181, k3_xboole_0(B_182, B_180))=k3_xboole_0(B_181, k3_xboole_0(B_182, B_180)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2125])).
% 12.06/5.25  tff(c_2533, plain, (![B_198, B_199, B_200]: (m1_subset_1(k3_xboole_0(B_198, k3_xboole_0(B_199, B_200)), k1_zfmisc_1(B_200)) | ~m1_subset_1(k3_xboole_0(B_199, B_200), k1_zfmisc_1(B_200)))), inference(superposition, [status(thm), theory('equality')], [c_2130, c_10])).
% 12.06/5.25  tff(c_2576, plain, (![B_198, B_85, B_86]: (m1_subset_1(k3_xboole_0(B_198, k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0(k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3')), u1_struct_0('#skF_1')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_602, c_2533])).
% 12.06/5.25  tff(c_2616, plain, (![B_198, B_85, B_86]: (m1_subset_1(k3_xboole_0(B_198, k3_xboole_0(B_85, k3_xboole_0(B_86, '#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_602, c_2576])).
% 12.06/5.25  tff(c_579, plain, (![B_83, B_84]: (r1_tarski(k3_xboole_0(B_83, k3_xboole_0(B_84, '#skF_3')), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_566])).
% 12.06/5.25  tff(c_143, plain, (![B_9, B_47]: (k9_subset_1(u1_struct_0('#skF_1'), B_9, k3_xboole_0(B_47, '#skF_3'))=k3_xboole_0(B_9, k3_xboole_0(B_47, '#skF_3')))), inference(resolution, [status(thm)], [c_133, c_12])).
% 12.06/5.25  tff(c_1281, plain, (![A_117, B_118, B_119, C_120]: (k9_subset_1(A_117, B_118, k9_subset_1(A_117, B_119, C_120))=k3_xboole_0(B_118, k9_subset_1(A_117, B_119, C_120)) | ~m1_subset_1(C_120, k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_120, c_12])).
% 12.06/5.25  tff(c_1291, plain, (![B_118, B_119, B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_118, k9_subset_1(u1_struct_0('#skF_1'), B_119, k3_xboole_0(B_41, '#skF_3')))=k3_xboole_0(B_118, k9_subset_1(u1_struct_0('#skF_1'), B_119, k3_xboole_0(B_41, '#skF_3'))))), inference(resolution, [status(thm)], [c_132, c_1281])).
% 12.06/5.25  tff(c_1306, plain, (![B_118, B_119, B_41]: (k9_subset_1(u1_struct_0('#skF_1'), B_118, k3_xboole_0(B_119, k3_xboole_0(B_41, '#skF_3')))=k3_xboole_0(B_118, k3_xboole_0(B_119, k3_xboole_0(B_41, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_1291])).
% 12.06/5.25  tff(c_3563, plain, (![B_250, B_251, B_252]: (k9_subset_1(u1_struct_0('#skF_1'), B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3')))=k3_xboole_0(B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_1291])).
% 12.06/5.25  tff(c_1117, plain, (![B_12, B_112, A_11]: (k3_xboole_0(k9_subset_1(B_12, B_112, A_11), B_12)=k9_subset_1(B_12, B_112, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_1090])).
% 12.06/5.25  tff(c_3587, plain, (![B_250, B_251, B_252]: (k3_xboole_0(k3_xboole_0(B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3'))), u1_struct_0('#skF_1'))=k9_subset_1(u1_struct_0('#skF_1'), B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3'))) | ~r1_tarski(k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3')), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3563, c_1117])).
% 12.06/5.25  tff(c_3635, plain, (![B_250, B_251, B_252]: (k3_xboole_0(k3_xboole_0(B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3'))), u1_struct_0('#skF_1'))=k3_xboole_0(B_250, k3_xboole_0(B_251, k3_xboole_0(B_252, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_1306, c_3587])).
% 12.06/5.25  tff(c_4553, plain, (![B_304, B_305, B_306]: (k3_xboole_0(k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_306, '#skF_3'))), u1_struct_0('#skF_1'))=k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_306, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_1306, c_3587])).
% 12.06/5.25  tff(c_2200, plain, (![B_181, B_182, B_180]: (r1_tarski(k3_xboole_0(B_181, k3_xboole_0(B_182, B_180)), B_180) | ~m1_subset_1(k3_xboole_0(B_182, B_180), k1_zfmisc_1(B_180)))), inference(superposition, [status(thm), theory('equality')], [c_2130, c_130])).
% 12.06/5.25  tff(c_4565, plain, (![B_181, B_304, B_305, B_306]: (r1_tarski(k3_xboole_0(B_181, k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_306, '#skF_3')))), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_xboole_0(k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_306, '#skF_3'))), u1_struct_0('#skF_1')), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4553, c_2200])).
% 12.06/5.25  tff(c_4626, plain, (![B_181, B_304, B_305, B_306]: (r1_tarski(k3_xboole_0(B_181, k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_306, '#skF_3')))), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2616, c_3635, c_4565])).
% 12.06/5.25  tff(c_7162, plain, (![B_378, B_305, B_377, B_304, B_181]: (r1_tarski(k3_xboole_0(B_181, k3_xboole_0(B_304, k3_xboole_0(B_305, k3_xboole_0(B_377, k3_xboole_0(B_378, '#skF_3'))))), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7012, c_4626])).
% 12.06/5.25  tff(c_11756, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7162])).
% 12.06/5.25  tff(c_11759, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_11756])).
% 12.06/5.25  tff(c_11763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11759])).
% 12.06/5.25  tff(c_11765, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7162])).
% 12.06/5.25  tff(c_1122, plain, (![B_114, B_115, A_116]: (k3_xboole_0(k9_subset_1(B_114, B_115, A_116), B_114)=k9_subset_1(B_114, B_115, A_116) | ~r1_tarski(A_116, B_114))), inference(resolution, [status(thm)], [c_16, c_1090])).
% 12.06/5.25  tff(c_1249, plain, (![B_115, A_116]: (m1_subset_1(k9_subset_1('#skF_3', B_115, A_116), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_116, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1122, c_132])).
% 12.06/5.25  tff(c_639, plain, (![C_89, A_90, B_91]: (v2_compts_1(C_89, A_90) | ~v4_pre_topc(C_89, A_90) | ~r1_tarski(C_89, B_91) | ~v2_compts_1(B_91, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.06/5.25  tff(c_8315, plain, (![A_399, B_400, C_401, A_402]: (v2_compts_1(k9_subset_1(A_399, B_400, C_401), A_402) | ~v4_pre_topc(k9_subset_1(A_399, B_400, C_401), A_402) | ~v2_compts_1(A_399, A_402) | ~m1_subset_1(k9_subset_1(A_399, B_400, C_401), k1_zfmisc_1(u1_struct_0(A_402))) | ~m1_subset_1(A_399, k1_zfmisc_1(u1_struct_0(A_402))) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | ~m1_subset_1(C_401, k1_zfmisc_1(A_399)))), inference(resolution, [status(thm)], [c_130, c_639])).
% 12.06/5.25  tff(c_8352, plain, (![B_115, A_116]: (v2_compts_1(k9_subset_1('#skF_3', B_115, A_116), '#skF_1') | ~v4_pre_topc(k9_subset_1('#skF_3', B_115, A_116), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1(A_116, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_116, '#skF_3'))), inference(resolution, [status(thm)], [c_1249, c_8315])).
% 12.06/5.25  tff(c_22672, plain, (![B_882, A_883]: (v2_compts_1(k9_subset_1('#skF_3', B_882, A_883), '#skF_1') | ~v4_pre_topc(k9_subset_1('#skF_3', B_882, A_883), '#skF_1') | ~m1_subset_1(A_883, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_883, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_26, c_8352])).
% 12.06/5.25  tff(c_22699, plain, (![B_55]: (v2_compts_1(k9_subset_1('#skF_3', B_55, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_55, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_22672])).
% 12.06/5.25  tff(c_22704, plain, (![B_884]: (v2_compts_1(k3_xboole_0(B_884, '#skF_3'), '#skF_1') | ~v4_pre_topc(k3_xboole_0(B_884, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11765, c_244, c_22699])).
% 12.06/5.25  tff(c_22793, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1676, c_22704])).
% 12.06/5.25  tff(c_22857, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_288, c_22793])).
% 12.06/5.25  tff(c_22859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_22857])).
% 12.06/5.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/5.25  
% 12.06/5.25  Inference rules
% 12.06/5.25  ----------------------
% 12.06/5.25  #Ref     : 0
% 12.06/5.25  #Sup     : 5298
% 12.06/5.25  #Fact    : 0
% 12.06/5.25  #Define  : 0
% 12.06/5.25  #Split   : 7
% 12.06/5.25  #Chain   : 0
% 12.06/5.25  #Close   : 0
% 12.06/5.25  
% 12.06/5.25  Ordering : KBO
% 12.06/5.25  
% 12.06/5.25  Simplification rules
% 12.06/5.25  ----------------------
% 12.06/5.25  #Subsume      : 840
% 12.06/5.25  #Demod        : 3328
% 12.06/5.25  #Tautology    : 963
% 12.06/5.25  #SimpNegUnit  : 2
% 12.06/5.25  #BackRed      : 1
% 12.06/5.25  
% 12.06/5.25  #Partial instantiations: 0
% 12.06/5.25  #Strategies tried      : 1
% 12.06/5.25  
% 12.06/5.25  Timing (in seconds)
% 12.06/5.25  ----------------------
% 12.06/5.25  Preprocessing        : 0.29
% 12.06/5.26  Parsing              : 0.15
% 12.06/5.26  CNF conversion       : 0.02
% 12.06/5.26  Main loop            : 4.11
% 12.06/5.26  Inferencing          : 1.05
% 12.06/5.26  Reduction            : 1.71
% 12.06/5.26  Demodulation         : 1.41
% 12.06/5.26  BG Simplification    : 0.12
% 12.06/5.26  Subsumption          : 1.01
% 12.06/5.26  Abstraction          : 0.16
% 12.06/5.26  MUC search           : 0.00
% 12.06/5.26  Cooper               : 0.00
% 12.06/5.26  Total                : 4.44
% 12.06/5.26  Index Insertion      : 0.00
% 12.06/5.26  Index Deletion       : 0.00
% 12.06/5.26  Index Matching       : 0.00
% 12.06/5.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
