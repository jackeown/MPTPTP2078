%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:02 EST 2020

% Result     : Theorem 21.58s
% Output     : CNFRefutation 21.58s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 396 expanded)
%              Number of leaves         :   37 ( 153 expanded)
%              Depth                    :   15
%              Number of atoms          :  154 ( 956 expanded)
%              Number of equality atoms :   32 ( 174 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v4_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v4_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v4_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_58,plain,(
    ~ v4_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_66,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_83,plain,(
    ! [B_96,A_97] :
      ( l1_pre_topc(B_96)
      | ~ m1_pre_topc(B_96,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_83])).

tff(c_89,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_86])).

tff(c_46,plain,(
    ! [A_57] :
      ( l1_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ! [A_95] :
      ( u1_struct_0(A_95) = k2_struct_0(A_95)
      | ~ l1_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [A_98] :
      ( u1_struct_0(A_98) = k2_struct_0(A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_46,c_78])).

tff(c_97,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_89,c_90])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_99,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_62])).

tff(c_149,plain,(
    ! [A_107,B_108,C_109] :
      ( k9_subset_1(A_107,B_108,C_109) = k3_xboole_0(B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_194,plain,(
    ! [B_116] : k9_subset_1(k2_struct_0('#skF_7'),B_116,'#skF_8') = k3_xboole_0(B_116,'#skF_8') ),
    inference(resolution,[status(thm)],[c_99,c_149])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k9_subset_1(A_6,B_7,C_8),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [B_116] :
      ( m1_subset_1(k3_xboole_0(B_116,'#skF_8'),k1_zfmisc_1(k2_struct_0('#skF_7')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_6])).

tff(c_208,plain,(
    ! [B_117] : m1_subset_1(k3_xboole_0(B_117,'#skF_8'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_200])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_215,plain,(
    ! [B_117] : r1_tarski(k3_xboole_0(B_117,'#skF_8'),k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_208,c_12])).

tff(c_98,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_90])).

tff(c_60,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_104,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_72])).

tff(c_119,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(A_103,B_104)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    r1_tarski('#skF_8',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_104,c_119])).

tff(c_64,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_71,plain,(
    v4_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64])).

tff(c_131,plain,(
    r1_tarski('#skF_8',k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_99,c_119])).

tff(c_132,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(A_105,B_106) = A_105
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_131,c_132])).

tff(c_461,plain,(
    ! [B_141,A_142] :
      ( r1_tarski(k2_struct_0(B_141),k2_struct_0(A_142))
      | ~ m1_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(B_141)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_157,plain,(
    ! [B_15,B_108,A_14] :
      ( k9_subset_1(B_15,B_108,A_14) = k3_xboole_0(B_108,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_4744,plain,(
    ! [A_526,B_527,B_528] :
      ( k9_subset_1(k2_struct_0(A_526),B_527,k2_struct_0(B_528)) = k3_xboole_0(B_527,k2_struct_0(B_528))
      | ~ m1_pre_topc(B_528,A_526)
      | ~ l1_pre_topc(B_528)
      | ~ l1_pre_topc(A_526) ) ),
    inference(resolution,[status(thm)],[c_461,c_157])).

tff(c_156,plain,(
    ! [B_108] : k9_subset_1(k2_struct_0('#skF_5'),B_108,'#skF_8') = k3_xboole_0(B_108,'#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_149])).

tff(c_254,plain,(
    ! [A_124,C_125,B_126] :
      ( k9_subset_1(A_124,C_125,B_126) = k9_subset_1(A_124,B_126,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_262,plain,(
    ! [B_126] : k9_subset_1(k2_struct_0('#skF_5'),B_126,'#skF_8') = k9_subset_1(k2_struct_0('#skF_5'),'#skF_8',B_126) ),
    inference(resolution,[status(thm)],[c_104,c_254])).

tff(c_271,plain,(
    ! [B_126] : k9_subset_1(k2_struct_0('#skF_5'),'#skF_8',B_126) = k3_xboole_0(B_126,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_262])).

tff(c_4790,plain,(
    ! [B_528] :
      ( k3_xboole_0(k2_struct_0(B_528),'#skF_8') = k3_xboole_0('#skF_8',k2_struct_0(B_528))
      | ~ m1_pre_topc(B_528,'#skF_5')
      | ~ l1_pre_topc(B_528)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4744,c_271])).

tff(c_5182,plain,(
    ! [B_536] :
      ( k3_xboole_0(k2_struct_0(B_536),'#skF_8') = k3_xboole_0('#skF_8',k2_struct_0(B_536))
      | ~ m1_pre_topc(B_536,'#skF_5')
      | ~ l1_pre_topc(B_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4790])).

tff(c_216,plain,(
    ! [B_118] : r1_tarski(k3_xboole_0(B_118,'#skF_8'),k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_208,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_220,plain,(
    ! [B_118] : k3_xboole_0(k3_xboole_0(B_118,'#skF_8'),k2_struct_0('#skF_7')) = k3_xboole_0(B_118,'#skF_8') ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_6129,plain,(
    ! [B_584] :
      ( k3_xboole_0(k3_xboole_0('#skF_8',k2_struct_0(B_584)),k2_struct_0('#skF_7')) = k3_xboole_0(k2_struct_0(B_584),'#skF_8')
      | ~ m1_pre_topc(B_584,'#skF_5')
      | ~ l1_pre_topc(B_584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5182,c_220])).

tff(c_6150,plain,
    ( k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8') = k3_xboole_0('#skF_8',k2_struct_0('#skF_7'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_6129])).

tff(c_6159,plain,(
    k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_66,c_140,c_6150])).

tff(c_158,plain,(
    ! [B_108] : k9_subset_1(k2_struct_0('#skF_7'),B_108,'#skF_8') = k3_xboole_0(B_108,'#skF_8') ),
    inference(resolution,[status(thm)],[c_99,c_149])).

tff(c_266,plain,(
    ! [B_126] : k9_subset_1(k2_struct_0('#skF_7'),B_126,'#skF_8') = k9_subset_1(k2_struct_0('#skF_7'),'#skF_8',B_126) ),
    inference(resolution,[status(thm)],[c_99,c_254])).

tff(c_274,plain,(
    ! [B_126] : k9_subset_1(k2_struct_0('#skF_7'),'#skF_8',B_126) = k3_xboole_0(B_126,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_266])).

tff(c_2885,plain,(
    ! [B_354,D_355,A_356] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_354),D_355,k2_struct_0(B_354)),B_354)
      | ~ v4_pre_topc(D_355,A_356)
      | ~ m1_subset_1(D_355,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_354),D_355,k2_struct_0(B_354)),k1_zfmisc_1(u1_struct_0(B_354)))
      | ~ m1_pre_topc(B_354,A_356)
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11596,plain,(
    ! [B_758,A_759,A_760] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_758),A_759,k2_struct_0(B_758)),B_758)
      | ~ v4_pre_topc(A_759,A_760)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_758),A_759,k2_struct_0(B_758)),k1_zfmisc_1(u1_struct_0(B_758)))
      | ~ m1_pre_topc(B_758,A_760)
      | ~ l1_pre_topc(A_760)
      | ~ r1_tarski(A_759,u1_struct_0(A_760)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2885])).

tff(c_38210,plain,(
    ! [B_1711,A_1712,A_1713] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_1711),A_1712,k2_struct_0(B_1711)),B_1711)
      | ~ v4_pre_topc(A_1712,A_1713)
      | ~ m1_pre_topc(B_1711,A_1713)
      | ~ l1_pre_topc(A_1713)
      | ~ r1_tarski(A_1712,u1_struct_0(A_1713))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(B_1711),A_1712,k2_struct_0(B_1711)),u1_struct_0(B_1711)) ) ),
    inference(resolution,[status(thm)],[c_14,c_11596])).

tff(c_38212,plain,(
    ! [A_1712] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),A_1712,k2_struct_0('#skF_7')),'#skF_7')
      | ~ v4_pre_topc(A_1712,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_1712,u1_struct_0('#skF_5'))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_7'),A_1712,k2_struct_0('#skF_7')),u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_66,c_38210])).

tff(c_38216,plain,(
    ! [A_1714] :
      ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_7'),A_1714,k2_struct_0('#skF_7')),'#skF_7')
      | ~ v4_pre_topc(A_1714,'#skF_5')
      | ~ r1_tarski(A_1714,k2_struct_0('#skF_5'))
      | ~ r1_tarski(k9_subset_1(k2_struct_0('#skF_7'),A_1714,k2_struct_0('#skF_7')),k2_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_98,c_70,c_97,c_38212])).

tff(c_38284,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ v4_pre_topc('#skF_8','#skF_5')
    | ~ r1_tarski('#skF_8',k2_struct_0('#skF_5'))
    | ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8'),k2_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_38216])).

tff(c_38320,plain,(
    v4_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_129,c_71,c_6159,c_274,c_38284])).

tff(c_38322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_38320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.58/11.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.58/11.53  
% 21.58/11.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.58/11.53  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 21.58/11.53  
% 21.58/11.53  %Foreground sorts:
% 21.58/11.53  
% 21.58/11.53  
% 21.58/11.53  %Background operators:
% 21.58/11.53  
% 21.58/11.53  
% 21.58/11.53  %Foreground operators:
% 21.58/11.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.58/11.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 21.58/11.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.58/11.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.58/11.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.58/11.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 21.58/11.53  tff('#skF_7', type, '#skF_7': $i).
% 21.58/11.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 21.58/11.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.58/11.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.58/11.53  tff('#skF_5', type, '#skF_5': $i).
% 21.58/11.53  tff('#skF_6', type, '#skF_6': $i).
% 21.58/11.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.58/11.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 21.58/11.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 21.58/11.53  tff('#skF_8', type, '#skF_8': $i).
% 21.58/11.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.58/11.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.58/11.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 21.58/11.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 21.58/11.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.58/11.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.58/11.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 21.58/11.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 21.58/11.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.58/11.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.58/11.53  
% 21.58/11.55  tff(f_118, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 21.58/11.55  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 21.58/11.55  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 21.58/11.55  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 21.58/11.55  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 21.58/11.55  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 21.58/11.55  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 21.58/11.55  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 21.58/11.55  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 21.58/11.55  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 21.58/11.55  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 21.58/11.55  tff(c_58, plain, (~v4_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_66, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_83, plain, (![B_96, A_97]: (l1_pre_topc(B_96) | ~m1_pre_topc(B_96, A_97) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.58/11.55  tff(c_86, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_83])).
% 21.58/11.55  tff(c_89, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_86])).
% 21.58/11.55  tff(c_46, plain, (![A_57]: (l1_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_76])).
% 21.58/11.55  tff(c_78, plain, (![A_95]: (u1_struct_0(A_95)=k2_struct_0(A_95) | ~l1_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.58/11.55  tff(c_90, plain, (![A_98]: (u1_struct_0(A_98)=k2_struct_0(A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_46, c_78])).
% 21.58/11.55  tff(c_97, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_89, c_90])).
% 21.58/11.55  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_99, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_62])).
% 21.58/11.55  tff(c_149, plain, (![A_107, B_108, C_109]: (k9_subset_1(A_107, B_108, C_109)=k3_xboole_0(B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.58/11.55  tff(c_194, plain, (![B_116]: (k9_subset_1(k2_struct_0('#skF_7'), B_116, '#skF_8')=k3_xboole_0(B_116, '#skF_8'))), inference(resolution, [status(thm)], [c_99, c_149])).
% 21.58/11.55  tff(c_6, plain, (![A_6, B_7, C_8]: (m1_subset_1(k9_subset_1(A_6, B_7, C_8), k1_zfmisc_1(A_6)) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 21.58/11.55  tff(c_200, plain, (![B_116]: (m1_subset_1(k3_xboole_0(B_116, '#skF_8'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_194, c_6])).
% 21.58/11.55  tff(c_208, plain, (![B_117]: (m1_subset_1(k3_xboole_0(B_117, '#skF_8'), k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_200])).
% 21.58/11.55  tff(c_12, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.58/11.55  tff(c_215, plain, (![B_117]: (r1_tarski(k3_xboole_0(B_117, '#skF_8'), k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_208, c_12])).
% 21.58/11.55  tff(c_98, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_90])).
% 21.58/11.55  tff(c_60, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 21.58/11.55  tff(c_104, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_72])).
% 21.58/11.55  tff(c_119, plain, (![A_103, B_104]: (r1_tarski(A_103, B_104) | ~m1_subset_1(A_103, k1_zfmisc_1(B_104)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.58/11.55  tff(c_129, plain, (r1_tarski('#skF_8', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_104, c_119])).
% 21.58/11.55  tff(c_64, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 21.58/11.55  tff(c_71, plain, (v4_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64])).
% 21.58/11.55  tff(c_131, plain, (r1_tarski('#skF_8', k2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_99, c_119])).
% 21.58/11.55  tff(c_132, plain, (![A_105, B_106]: (k3_xboole_0(A_105, B_106)=A_105 | ~r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.58/11.55  tff(c_140, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_131, c_132])).
% 21.58/11.55  tff(c_461, plain, (![B_141, A_142]: (r1_tarski(k2_struct_0(B_141), k2_struct_0(A_142)) | ~m1_pre_topc(B_141, A_142) | ~l1_pre_topc(B_141) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.58/11.55  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.58/11.55  tff(c_157, plain, (![B_15, B_108, A_14]: (k9_subset_1(B_15, B_108, A_14)=k3_xboole_0(B_108, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_14, c_149])).
% 21.58/11.55  tff(c_4744, plain, (![A_526, B_527, B_528]: (k9_subset_1(k2_struct_0(A_526), B_527, k2_struct_0(B_528))=k3_xboole_0(B_527, k2_struct_0(B_528)) | ~m1_pre_topc(B_528, A_526) | ~l1_pre_topc(B_528) | ~l1_pre_topc(A_526))), inference(resolution, [status(thm)], [c_461, c_157])).
% 21.58/11.55  tff(c_156, plain, (![B_108]: (k9_subset_1(k2_struct_0('#skF_5'), B_108, '#skF_8')=k3_xboole_0(B_108, '#skF_8'))), inference(resolution, [status(thm)], [c_104, c_149])).
% 21.58/11.55  tff(c_254, plain, (![A_124, C_125, B_126]: (k9_subset_1(A_124, C_125, B_126)=k9_subset_1(A_124, B_126, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.58/11.55  tff(c_262, plain, (![B_126]: (k9_subset_1(k2_struct_0('#skF_5'), B_126, '#skF_8')=k9_subset_1(k2_struct_0('#skF_5'), '#skF_8', B_126))), inference(resolution, [status(thm)], [c_104, c_254])).
% 21.58/11.55  tff(c_271, plain, (![B_126]: (k9_subset_1(k2_struct_0('#skF_5'), '#skF_8', B_126)=k3_xboole_0(B_126, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_262])).
% 21.58/11.55  tff(c_4790, plain, (![B_528]: (k3_xboole_0(k2_struct_0(B_528), '#skF_8')=k3_xboole_0('#skF_8', k2_struct_0(B_528)) | ~m1_pre_topc(B_528, '#skF_5') | ~l1_pre_topc(B_528) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4744, c_271])).
% 21.58/11.55  tff(c_5182, plain, (![B_536]: (k3_xboole_0(k2_struct_0(B_536), '#skF_8')=k3_xboole_0('#skF_8', k2_struct_0(B_536)) | ~m1_pre_topc(B_536, '#skF_5') | ~l1_pre_topc(B_536))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4790])).
% 21.58/11.55  tff(c_216, plain, (![B_118]: (r1_tarski(k3_xboole_0(B_118, '#skF_8'), k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_208, c_12])).
% 21.58/11.55  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 21.58/11.55  tff(c_220, plain, (![B_118]: (k3_xboole_0(k3_xboole_0(B_118, '#skF_8'), k2_struct_0('#skF_7'))=k3_xboole_0(B_118, '#skF_8'))), inference(resolution, [status(thm)], [c_216, c_2])).
% 21.58/11.55  tff(c_6129, plain, (![B_584]: (k3_xboole_0(k3_xboole_0('#skF_8', k2_struct_0(B_584)), k2_struct_0('#skF_7'))=k3_xboole_0(k2_struct_0(B_584), '#skF_8') | ~m1_pre_topc(B_584, '#skF_5') | ~l1_pre_topc(B_584))), inference(superposition, [status(thm), theory('equality')], [c_5182, c_220])).
% 21.58/11.55  tff(c_6150, plain, (k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8')=k3_xboole_0('#skF_8', k2_struct_0('#skF_7')) | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_140, c_6129])).
% 21.58/11.55  tff(c_6159, plain, (k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_66, c_140, c_6150])).
% 21.58/11.55  tff(c_158, plain, (![B_108]: (k9_subset_1(k2_struct_0('#skF_7'), B_108, '#skF_8')=k3_xboole_0(B_108, '#skF_8'))), inference(resolution, [status(thm)], [c_99, c_149])).
% 21.58/11.55  tff(c_266, plain, (![B_126]: (k9_subset_1(k2_struct_0('#skF_7'), B_126, '#skF_8')=k9_subset_1(k2_struct_0('#skF_7'), '#skF_8', B_126))), inference(resolution, [status(thm)], [c_99, c_254])).
% 21.58/11.55  tff(c_274, plain, (![B_126]: (k9_subset_1(k2_struct_0('#skF_7'), '#skF_8', B_126)=k3_xboole_0(B_126, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_266])).
% 21.58/11.55  tff(c_2885, plain, (![B_354, D_355, A_356]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_354), D_355, k2_struct_0(B_354)), B_354) | ~v4_pre_topc(D_355, A_356) | ~m1_subset_1(D_355, k1_zfmisc_1(u1_struct_0(A_356))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_354), D_355, k2_struct_0(B_354)), k1_zfmisc_1(u1_struct_0(B_354))) | ~m1_pre_topc(B_354, A_356) | ~l1_pre_topc(A_356))), inference(cnfTransformation, [status(thm)], [f_100])).
% 21.58/11.55  tff(c_11596, plain, (![B_758, A_759, A_760]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_758), A_759, k2_struct_0(B_758)), B_758) | ~v4_pre_topc(A_759, A_760) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_758), A_759, k2_struct_0(B_758)), k1_zfmisc_1(u1_struct_0(B_758))) | ~m1_pre_topc(B_758, A_760) | ~l1_pre_topc(A_760) | ~r1_tarski(A_759, u1_struct_0(A_760)))), inference(resolution, [status(thm)], [c_14, c_2885])).
% 21.58/11.55  tff(c_38210, plain, (![B_1711, A_1712, A_1713]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_1711), A_1712, k2_struct_0(B_1711)), B_1711) | ~v4_pre_topc(A_1712, A_1713) | ~m1_pre_topc(B_1711, A_1713) | ~l1_pre_topc(A_1713) | ~r1_tarski(A_1712, u1_struct_0(A_1713)) | ~r1_tarski(k9_subset_1(u1_struct_0(B_1711), A_1712, k2_struct_0(B_1711)), u1_struct_0(B_1711)))), inference(resolution, [status(thm)], [c_14, c_11596])).
% 21.58/11.55  tff(c_38212, plain, (![A_1712]: (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), A_1712, k2_struct_0('#skF_7')), '#skF_7') | ~v4_pre_topc(A_1712, '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski(A_1712, u1_struct_0('#skF_5')) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_7'), A_1712, k2_struct_0('#skF_7')), u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_66, c_38210])).
% 21.58/11.55  tff(c_38216, plain, (![A_1714]: (v4_pre_topc(k9_subset_1(k2_struct_0('#skF_7'), A_1714, k2_struct_0('#skF_7')), '#skF_7') | ~v4_pre_topc(A_1714, '#skF_5') | ~r1_tarski(A_1714, k2_struct_0('#skF_5')) | ~r1_tarski(k9_subset_1(k2_struct_0('#skF_7'), A_1714, k2_struct_0('#skF_7')), k2_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_98, c_70, c_97, c_38212])).
% 21.58/11.55  tff(c_38284, plain, (v4_pre_topc(k9_subset_1(k2_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~v4_pre_topc('#skF_8', '#skF_5') | ~r1_tarski('#skF_8', k2_struct_0('#skF_5')) | ~r1_tarski(k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8'), k2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_38216])).
% 21.58/11.55  tff(c_38320, plain, (v4_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_129, c_71, c_6159, c_274, c_38284])).
% 21.58/11.55  tff(c_38322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_38320])).
% 21.58/11.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.58/11.55  
% 21.58/11.55  Inference rules
% 21.58/11.55  ----------------------
% 21.58/11.55  #Ref     : 0
% 21.58/11.55  #Sup     : 11164
% 21.58/11.55  #Fact    : 0
% 21.58/11.55  #Define  : 0
% 21.58/11.55  #Split   : 6
% 21.58/11.55  #Chain   : 0
% 21.58/11.55  #Close   : 0
% 21.58/11.55  
% 21.58/11.55  Ordering : KBO
% 21.58/11.55  
% 21.58/11.55  Simplification rules
% 21.58/11.55  ----------------------
% 21.58/11.55  #Subsume      : 848
% 21.58/11.55  #Demod        : 3993
% 21.58/11.55  #Tautology    : 2294
% 21.58/11.55  #SimpNegUnit  : 5
% 21.58/11.55  #BackRed      : 2
% 21.58/11.55  
% 21.58/11.55  #Partial instantiations: 0
% 21.58/11.55  #Strategies tried      : 1
% 21.58/11.55  
% 21.58/11.55  Timing (in seconds)
% 21.58/11.55  ----------------------
% 21.58/11.55  Preprocessing        : 0.36
% 21.58/11.55  Parsing              : 0.18
% 21.58/11.55  CNF conversion       : 0.03
% 21.58/11.55  Main loop            : 10.40
% 21.58/11.55  Inferencing          : 2.30
% 21.58/11.55  Reduction            : 4.42
% 21.58/11.55  Demodulation         : 3.77
% 21.58/11.55  BG Simplification    : 0.30
% 21.58/11.55  Subsumption          : 2.78
% 21.58/11.55  Abstraction          : 0.43
% 21.58/11.55  MUC search           : 0.00
% 21.58/11.55  Cooper               : 0.00
% 21.58/11.55  Total                : 10.80
% 21.58/11.55  Index Insertion      : 0.00
% 21.58/11.55  Index Deletion       : 0.00
% 21.58/11.55  Index Matching       : 0.00
% 21.58/11.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
