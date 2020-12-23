%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 21.90s
% Output     : CNFRefutation 21.90s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 129 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 401 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

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

tff(f_132,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_113,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_172,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,C_63) = k3_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_1'),B_62,'#skF_3') = k3_xboole_0(B_62,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_172])).

tff(c_30,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_237,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_30])).

tff(c_82,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1012,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | ~ v2_compts_1(B_105,A_106)
      | ~ v8_pre_topc(A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1037,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1012])).

tff(c_1046,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_34,c_1037])).

tff(c_32,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1040,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1012])).

tff(c_1049,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_32,c_1040])).

tff(c_1274,plain,(
    ! [B_118,C_119,A_120] :
      ( v4_pre_topc(k3_xboole_0(B_118,C_119),A_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v4_pre_topc(C_119,A_120)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v4_pre_topc(B_118,A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1293,plain,(
    ! [B_118] :
      ( v4_pre_topc(k3_xboole_0(B_118,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_118,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_1274])).

tff(c_1566,plain,(
    ! [B_135] :
      ( v4_pre_topc(k3_xboole_0(B_135,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_135,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1049,c_1293])).

tff(c_1581,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1566])).

tff(c_1594,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_1581])).

tff(c_517,plain,(
    ! [A_83,B_84] :
      ( u1_struct_0(k1_pre_topc(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_524,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_517])).

tff(c_531,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_524])).

tff(c_769,plain,(
    ! [A_91,B_92] :
      ( m1_pre_topc(k1_pre_topc(A_91,B_92),A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_778,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_769])).

tff(c_784,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_778])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_794,plain,(
    ! [C_93,A_94,B_95] :
      ( m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(B_95)))
      | ~ m1_pre_topc(B_95,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1712,plain,(
    ! [A_140,A_141,B_142] :
      ( m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_pre_topc(B_142,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ r1_tarski(A_140,u1_struct_0(B_142)) ) ),
    inference(resolution,[status(thm)],[c_14,c_794])).

tff(c_1724,plain,(
    ! [A_140] :
      ( m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_140,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_784,c_1712])).

tff(c_1734,plain,(
    ! [A_140] :
      ( m1_subset_1(A_140,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_140,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_42,c_1724])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1526,plain,(
    ! [C_132,A_133,B_134] :
      ( v2_compts_1(C_132,A_133)
      | ~ v4_pre_topc(C_132,A_133)
      | ~ r1_tarski(C_132,B_134)
      | ~ v2_compts_1(B_134,A_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2739,plain,(
    ! [A_171,B_172,A_173] :
      ( v2_compts_1(k4_xboole_0(A_171,B_172),A_173)
      | ~ v4_pre_topc(k4_xboole_0(A_171,B_172),A_173)
      | ~ v2_compts_1(A_171,A_173)
      | ~ m1_subset_1(k4_xboole_0(A_171,B_172),k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(A_171,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_4,c_1526])).

tff(c_2774,plain,(
    ! [A_5,B_6,A_173] :
      ( v2_compts_1(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_173)
      | ~ v4_pre_topc(k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)),A_173)
      | ~ v2_compts_1(A_5,A_173)
      | ~ m1_subset_1(k3_xboole_0(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ m1_subset_1(A_5,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2739])).

tff(c_14860,plain,(
    ! [A_354,B_355,A_356] :
      ( v2_compts_1(k3_xboole_0(A_354,B_355),A_356)
      | ~ v4_pre_topc(k3_xboole_0(A_354,B_355),A_356)
      | ~ v2_compts_1(A_354,A_356)
      | ~ m1_subset_1(k3_xboole_0(A_354,B_355),k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ m1_subset_1(A_354,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_2774])).

tff(c_15003,plain,(
    ! [A_354,B_355] :
      ( v2_compts_1(k3_xboole_0(A_354,B_355),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_354,B_355),'#skF_1')
      | ~ v2_compts_1(A_354,'#skF_1')
      | ~ m1_subset_1(A_354,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_354,B_355),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1734,c_14860])).

tff(c_80510,plain,(
    ! [A_957,B_958] :
      ( v2_compts_1(k3_xboole_0(A_957,B_958),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_957,B_958),'#skF_1')
      | ~ v2_compts_1(A_957,'#skF_1')
      | ~ m1_subset_1(A_957,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_957,B_958),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_15003])).

tff(c_80728,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1594,c_80510])).

tff(c_80882,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_40,c_34,c_80728])).

tff(c_80884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_80882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n003.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 20:21:42 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.90/12.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.90/12.53  
% 21.90/12.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.90/12.53  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 21.90/12.53  
% 21.90/12.53  %Foreground sorts:
% 21.90/12.53  
% 21.90/12.53  
% 21.90/12.53  %Background operators:
% 21.90/12.53  
% 21.90/12.53  
% 21.90/12.53  %Foreground operators:
% 21.90/12.53  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 21.90/12.53  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 21.90/12.53  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 21.90/12.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.90/12.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.90/12.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.90/12.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.90/12.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.90/12.53  tff('#skF_2', type, '#skF_2': $i).
% 21.90/12.53  tff('#skF_3', type, '#skF_3': $i).
% 21.90/12.53  tff('#skF_1', type, '#skF_1': $i).
% 21.90/12.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 21.90/12.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.90/12.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.90/12.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.90/12.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.90/12.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 21.90/12.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.90/12.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.90/12.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.90/12.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.90/12.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.90/12.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.90/12.53  
% 21.90/12.55  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 21.90/12.55  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.90/12.55  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.90/12.55  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.90/12.55  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 21.90/12.55  tff(f_82, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tops_1)).
% 21.90/12.55  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 21.90/12.55  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 21.90/12.55  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.90/12.55  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 21.90/12.55  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 21.90/12.55  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_172, plain, (![A_61, B_62, C_63]: (k9_subset_1(A_61, B_62, C_63)=k3_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.90/12.55  tff(c_181, plain, (![B_62]: (k9_subset_1(u1_struct_0('#skF_1'), B_62, '#skF_3')=k3_xboole_0(B_62, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_172])).
% 21.90/12.55  tff(c_30, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_237, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_30])).
% 21.90/12.55  tff(c_82, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.90/12.55  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.90/12.55  tff(c_91, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4])).
% 21.90/12.55  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_34, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_36, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_1012, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | ~v2_compts_1(B_105, A_106) | ~v8_pre_topc(A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_95])).
% 21.90/12.55  tff(c_1037, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1012])).
% 21.90/12.55  tff(c_1046, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_1037])).
% 21.90/12.55  tff(c_32, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 21.90/12.55  tff(c_1040, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1012])).
% 21.90/12.55  tff(c_1049, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_1040])).
% 21.90/12.55  tff(c_1274, plain, (![B_118, C_119, A_120]: (v4_pre_topc(k3_xboole_0(B_118, C_119), A_120) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~v4_pre_topc(C_119, A_120) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_120))) | ~v4_pre_topc(B_118, A_120) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_82])).
% 21.90/12.55  tff(c_1293, plain, (![B_118]: (v4_pre_topc(k3_xboole_0(B_118, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_118, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_1274])).
% 21.90/12.55  tff(c_1566, plain, (![B_135]: (v4_pre_topc(k3_xboole_0(B_135, '#skF_3'), '#skF_1') | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_135, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1049, c_1293])).
% 21.90/12.55  tff(c_1581, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_1566])).
% 21.90/12.55  tff(c_1594, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_1581])).
% 21.90/12.55  tff(c_517, plain, (![A_83, B_84]: (u1_struct_0(k1_pre_topc(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.90/12.55  tff(c_524, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_517])).
% 21.90/12.55  tff(c_531, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_524])).
% 21.90/12.55  tff(c_769, plain, (![A_91, B_92]: (m1_pre_topc(k1_pre_topc(A_91, B_92), A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.90/12.55  tff(c_778, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_769])).
% 21.90/12.55  tff(c_784, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_778])).
% 21.90/12.55  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.90/12.55  tff(c_794, plain, (![C_93, A_94, B_95]: (m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(B_95))) | ~m1_pre_topc(B_95, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_68])).
% 21.90/12.55  tff(c_1712, plain, (![A_140, A_141, B_142]: (m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_pre_topc(B_142, A_141) | ~l1_pre_topc(A_141) | ~r1_tarski(A_140, u1_struct_0(B_142)))), inference(resolution, [status(thm)], [c_14, c_794])).
% 21.90/12.55  tff(c_1724, plain, (![A_140]: (m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_140, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_784, c_1712])).
% 21.90/12.55  tff(c_1734, plain, (![A_140]: (m1_subset_1(A_140, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_140, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_42, c_1724])).
% 21.90/12.55  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.90/12.55  tff(c_1526, plain, (![C_132, A_133, B_134]: (v2_compts_1(C_132, A_133) | ~v4_pre_topc(C_132, A_133) | ~r1_tarski(C_132, B_134) | ~v2_compts_1(B_134, A_133) | ~m1_subset_1(C_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_113])).
% 21.90/12.55  tff(c_2739, plain, (![A_171, B_172, A_173]: (v2_compts_1(k4_xboole_0(A_171, B_172), A_173) | ~v4_pre_topc(k4_xboole_0(A_171, B_172), A_173) | ~v2_compts_1(A_171, A_173) | ~m1_subset_1(k4_xboole_0(A_171, B_172), k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(A_171, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173))), inference(resolution, [status(thm)], [c_4, c_1526])).
% 21.90/12.55  tff(c_2774, plain, (![A_5, B_6, A_173]: (v2_compts_1(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_173) | ~v4_pre_topc(k4_xboole_0(A_5, k4_xboole_0(A_5, B_6)), A_173) | ~v2_compts_1(A_5, A_173) | ~m1_subset_1(k3_xboole_0(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_173))) | ~m1_subset_1(A_5, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2739])).
% 21.90/12.55  tff(c_14860, plain, (![A_354, B_355, A_356]: (v2_compts_1(k3_xboole_0(A_354, B_355), A_356) | ~v4_pre_topc(k3_xboole_0(A_354, B_355), A_356) | ~v2_compts_1(A_354, A_356) | ~m1_subset_1(k3_xboole_0(A_354, B_355), k1_zfmisc_1(u1_struct_0(A_356))) | ~m1_subset_1(A_354, k1_zfmisc_1(u1_struct_0(A_356))) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_2774])).
% 21.90/12.55  tff(c_15003, plain, (![A_354, B_355]: (v2_compts_1(k3_xboole_0(A_354, B_355), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_354, B_355), '#skF_1') | ~v2_compts_1(A_354, '#skF_1') | ~m1_subset_1(A_354, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_354, B_355), '#skF_2'))), inference(resolution, [status(thm)], [c_1734, c_14860])).
% 21.90/12.55  tff(c_80510, plain, (![A_957, B_958]: (v2_compts_1(k3_xboole_0(A_957, B_958), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_957, B_958), '#skF_1') | ~v2_compts_1(A_957, '#skF_1') | ~m1_subset_1(A_957, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_957, B_958), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_15003])).
% 21.90/12.55  tff(c_80728, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1594, c_80510])).
% 21.90/12.55  tff(c_80882, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_40, c_34, c_80728])).
% 21.90/12.55  tff(c_80884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_80882])).
% 21.90/12.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.90/12.55  
% 21.90/12.55  Inference rules
% 21.90/12.55  ----------------------
% 21.90/12.55  #Ref     : 0
% 21.90/12.55  #Sup     : 18850
% 21.90/12.55  #Fact    : 0
% 21.90/12.55  #Define  : 0
% 21.90/12.55  #Split   : 12
% 21.90/12.55  #Chain   : 0
% 21.90/12.55  #Close   : 0
% 21.90/12.55  
% 21.90/12.55  Ordering : KBO
% 21.90/12.55  
% 21.90/12.55  Simplification rules
% 21.90/12.55  ----------------------
% 21.90/12.55  #Subsume      : 5604
% 21.90/12.55  #Demod        : 22307
% 21.90/12.55  #Tautology    : 5766
% 21.90/12.55  #SimpNegUnit  : 109
% 21.90/12.55  #BackRed      : 1
% 21.90/12.55  
% 21.90/12.55  #Partial instantiations: 0
% 21.90/12.55  #Strategies tried      : 1
% 21.90/12.55  
% 21.90/12.55  Timing (in seconds)
% 21.90/12.55  ----------------------
% 21.90/12.55  Preprocessing        : 0.33
% 21.90/12.55  Parsing              : 0.19
% 21.90/12.55  CNF conversion       : 0.02
% 21.90/12.55  Main loop            : 11.62
% 21.90/12.55  Inferencing          : 2.12
% 21.90/12.55  Reduction            : 5.16
% 21.90/12.55  Demodulation         : 4.26
% 21.90/12.55  BG Simplification    : 0.21
% 21.90/12.55  Subsumption          : 3.55
% 21.90/12.55  Abstraction          : 0.33
% 21.90/12.55  MUC search           : 0.00
% 21.90/12.55  Cooper               : 0.00
% 21.90/12.55  Total                : 11.98
% 21.90/12.55  Index Insertion      : 0.00
% 21.90/12.55  Index Deletion       : 0.00
% 21.90/12.55  Index Matching       : 0.00
% 21.90/12.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
