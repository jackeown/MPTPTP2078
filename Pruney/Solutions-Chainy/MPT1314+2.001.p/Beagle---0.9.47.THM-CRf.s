%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:59 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 372 expanded)
%              Number of leaves         :   38 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 (1054 expanded)
%              Number of equality atoms :   30 ( 137 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_76,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_58,plain,(
    ~ v3_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_66,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_70,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_110,plain,(
    ! [B_100,A_101] :
      ( l1_pre_topc(B_100)
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_113,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_110])).

tff(c_116,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_113])).

tff(c_276,plain,(
    ! [A_124,B_125] :
      ( m1_pre_topc(k1_pre_topc(A_124,B_125),A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_278,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_276])).

tff(c_283,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_278])).

tff(c_48,plain,(
    ! [B_64,A_62] :
      ( l1_pre_topc(B_64)
      | ~ m1_pre_topc(B_64,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_289,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_283,c_48])).

tff(c_292,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_289])).

tff(c_215,plain,(
    ! [A_115,B_116] :
      ( v1_pre_topc(k1_pre_topc(A_115,B_116))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_218,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_215])).

tff(c_224,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_218])).

tff(c_435,plain,(
    ! [A_151,B_152] :
      ( k2_struct_0(k1_pre_topc(A_151,B_152)) = B_152
      | ~ m1_pre_topc(k1_pre_topc(A_151,B_152),A_151)
      | ~ v1_pre_topc(k1_pre_topc(A_151,B_152))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_439,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_283,c_435])).

tff(c_445,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_62,c_224,c_439])).

tff(c_271,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(k2_struct_0(B_122),k2_struct_0(A_123))
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(B_122)
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_275,plain,(
    ! [B_122,A_123] :
      ( k3_xboole_0(k2_struct_0(B_122),k2_struct_0(A_123)) = k2_struct_0(B_122)
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(B_122)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_271,c_2])).

tff(c_536,plain,(
    ! [A_123] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_123)) = k2_struct_0(k1_pre_topc('#skF_7','#skF_8'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_123)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_275])).

tff(c_632,plain,(
    ! [A_164] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_164)) = '#skF_8'
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_445,c_536])).

tff(c_635,plain,
    ( k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8'
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_283,c_632])).

tff(c_638,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_635])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_102,B_103] : k1_setfam_1(k2_tarski(A_102,B_103)) = k3_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [B_106,A_107] : k1_setfam_1(k2_tarski(B_106,A_107)) = k3_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [B_106,A_107] : k3_xboole_0(B_106,A_107) = k3_xboole_0(A_107,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_10])).

tff(c_189,plain,(
    ! [A_110,B_111,C_112] :
      ( k9_subset_1(A_110,B_111,C_112) = k3_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_194,plain,(
    ! [B_111] : k9_subset_1(u1_struct_0('#skF_7'),B_111,'#skF_8') = k3_xboole_0(B_111,'#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_228,plain,(
    ! [A_117,C_118,B_119] :
      ( k9_subset_1(A_117,C_118,B_119) = k9_subset_1(A_117,B_119,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_230,plain,(
    ! [B_119] : k9_subset_1(u1_struct_0('#skF_7'),B_119,'#skF_8') = k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_119) ),
    inference(resolution,[status(thm)],[c_62,c_228])).

tff(c_234,plain,(
    ! [B_119] : k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_119) = k3_xboole_0(B_119,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_230])).

tff(c_60,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_71,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_1101,plain,(
    ! [B_225,D_226,A_227] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_225),D_226,k2_struct_0(B_225)),B_225)
      | ~ v3_pre_topc(D_226,A_227)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_225),D_226,k2_struct_0(B_225)),k1_zfmisc_1(u1_struct_0(B_225)))
      | ~ m1_pre_topc(B_225,A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1113,plain,(
    ! [B_225] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_225),'#skF_8',k2_struct_0(B_225)),B_225)
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_225),'#skF_8',k2_struct_0(B_225)),k1_zfmisc_1(u1_struct_0(B_225)))
      | ~ m1_pre_topc(B_225,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_1101])).

tff(c_1124,plain,(
    ! [B_228] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_228),'#skF_8',k2_struct_0(B_228)),B_228)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_228),'#skF_8',k2_struct_0(B_228)),k1_zfmisc_1(u1_struct_0(B_228)))
      | ~ m1_pre_topc(B_228,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_71,c_1113])).

tff(c_1138,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1124])).

tff(c_1145,plain,(
    v3_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_638,c_139,c_638,c_139,c_234,c_1138])).

tff(c_1147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.61  
% 3.76/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.61  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 3.76/1.61  
% 3.76/1.61  %Foreground sorts:
% 3.76/1.61  
% 3.76/1.61  
% 3.76/1.61  %Background operators:
% 3.76/1.61  
% 3.76/1.61  
% 3.76/1.61  %Foreground operators:
% 3.76/1.61  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.76/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.76/1.61  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.76/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.76/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.76/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.76/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.76/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.76/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.76/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.76/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.76/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.76/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.76/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.76/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.76/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.76/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.76/1.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.76/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.76/1.61  
% 3.76/1.62  tff(f_126, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 3.76/1.62  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.76/1.62  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.76/1.62  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 3.76/1.62  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.76/1.62  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.76/1.62  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.76/1.62  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.76/1.62  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.76/1.62  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.76/1.62  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 3.76/1.62  tff(c_58, plain, (~v3_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_66, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_70, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_110, plain, (![B_100, A_101]: (l1_pre_topc(B_100) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.62  tff(c_113, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_110])).
% 3.76/1.62  tff(c_116, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_113])).
% 3.76/1.62  tff(c_276, plain, (![A_124, B_125]: (m1_pre_topc(k1_pre_topc(A_124, B_125), A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.76/1.62  tff(c_278, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_62, c_276])).
% 3.76/1.62  tff(c_283, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_278])).
% 3.76/1.62  tff(c_48, plain, (![B_64, A_62]: (l1_pre_topc(B_64) | ~m1_pre_topc(B_64, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.62  tff(c_289, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_283, c_48])).
% 3.76/1.62  tff(c_292, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_289])).
% 3.76/1.62  tff(c_215, plain, (![A_115, B_116]: (v1_pre_topc(k1_pre_topc(A_115, B_116)) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.76/1.62  tff(c_218, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_62, c_215])).
% 3.76/1.62  tff(c_224, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_218])).
% 3.76/1.62  tff(c_435, plain, (![A_151, B_152]: (k2_struct_0(k1_pre_topc(A_151, B_152))=B_152 | ~m1_pre_topc(k1_pre_topc(A_151, B_152), A_151) | ~v1_pre_topc(k1_pre_topc(A_151, B_152)) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.76/1.62  tff(c_439, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_283, c_435])).
% 3.76/1.62  tff(c_445, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_62, c_224, c_439])).
% 3.76/1.62  tff(c_271, plain, (![B_122, A_123]: (r1_tarski(k2_struct_0(B_122), k2_struct_0(A_123)) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(B_122) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.76/1.62  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.76/1.62  tff(c_275, plain, (![B_122, A_123]: (k3_xboole_0(k2_struct_0(B_122), k2_struct_0(A_123))=k2_struct_0(B_122) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(B_122) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_271, c_2])).
% 3.76/1.62  tff(c_536, plain, (![A_123]: (k3_xboole_0('#skF_8', k2_struct_0(A_123))=k2_struct_0(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_123) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_445, c_275])).
% 3.76/1.62  tff(c_632, plain, (![A_164]: (k3_xboole_0('#skF_8', k2_struct_0(A_164))='#skF_8' | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_164) | ~l1_pre_topc(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_445, c_536])).
% 3.76/1.62  tff(c_635, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8' | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_283, c_632])).
% 3.76/1.62  tff(c_638, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_635])).
% 3.76/1.62  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.62  tff(c_117, plain, (![A_102, B_103]: (k1_setfam_1(k2_tarski(A_102, B_103))=k3_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.76/1.62  tff(c_133, plain, (![B_106, A_107]: (k1_setfam_1(k2_tarski(B_106, A_107))=k3_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_4, c_117])).
% 3.76/1.62  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.76/1.62  tff(c_139, plain, (![B_106, A_107]: (k3_xboole_0(B_106, A_107)=k3_xboole_0(A_107, B_106))), inference(superposition, [status(thm), theory('equality')], [c_133, c_10])).
% 3.76/1.62  tff(c_189, plain, (![A_110, B_111, C_112]: (k9_subset_1(A_110, B_111, C_112)=k3_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.76/1.62  tff(c_194, plain, (![B_111]: (k9_subset_1(u1_struct_0('#skF_7'), B_111, '#skF_8')=k3_xboole_0(B_111, '#skF_8'))), inference(resolution, [status(thm)], [c_62, c_189])).
% 3.76/1.62  tff(c_228, plain, (![A_117, C_118, B_119]: (k9_subset_1(A_117, C_118, B_119)=k9_subset_1(A_117, B_119, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.76/1.62  tff(c_230, plain, (![B_119]: (k9_subset_1(u1_struct_0('#skF_7'), B_119, '#skF_8')=k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_119))), inference(resolution, [status(thm)], [c_62, c_228])).
% 3.76/1.62  tff(c_234, plain, (![B_119]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_119)=k3_xboole_0(B_119, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_230])).
% 3.76/1.62  tff(c_60, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_64, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_71, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64])).
% 3.76/1.62  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.76/1.62  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 3.76/1.62  tff(c_1101, plain, (![B_225, D_226, A_227]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_225), D_226, k2_struct_0(B_225)), B_225) | ~v3_pre_topc(D_226, A_227) | ~m1_subset_1(D_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_225), D_226, k2_struct_0(B_225)), k1_zfmisc_1(u1_struct_0(B_225))) | ~m1_pre_topc(B_225, A_227) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.76/1.62  tff(c_1113, plain, (![B_225]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_225), '#skF_8', k2_struct_0(B_225)), B_225) | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0(B_225), '#skF_8', k2_struct_0(B_225)), k1_zfmisc_1(u1_struct_0(B_225))) | ~m1_pre_topc(B_225, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_1101])).
% 3.76/1.62  tff(c_1124, plain, (![B_228]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_228), '#skF_8', k2_struct_0(B_228)), B_228) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_228), '#skF_8', k2_struct_0(B_228)), k1_zfmisc_1(u1_struct_0(B_228))) | ~m1_pre_topc(B_228, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_71, c_1113])).
% 3.76/1.62  tff(c_1138, plain, (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_234, c_1124])).
% 3.76/1.62  tff(c_1145, plain, (v3_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_638, c_139, c_638, c_139, c_234, c_1138])).
% 3.76/1.62  tff(c_1147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1145])).
% 3.76/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.62  
% 3.76/1.62  Inference rules
% 3.76/1.62  ----------------------
% 3.76/1.62  #Ref     : 0
% 3.76/1.62  #Sup     : 241
% 3.76/1.62  #Fact    : 0
% 3.76/1.62  #Define  : 0
% 3.76/1.62  #Split   : 11
% 3.76/1.62  #Chain   : 0
% 3.76/1.62  #Close   : 0
% 3.76/1.62  
% 3.76/1.62  Ordering : KBO
% 3.76/1.62  
% 3.76/1.62  Simplification rules
% 3.76/1.62  ----------------------
% 3.76/1.62  #Subsume      : 36
% 3.76/1.62  #Demod        : 148
% 3.76/1.62  #Tautology    : 65
% 3.76/1.62  #SimpNegUnit  : 5
% 3.76/1.63  #BackRed      : 0
% 3.76/1.63  
% 3.76/1.63  #Partial instantiations: 0
% 3.76/1.63  #Strategies tried      : 1
% 3.76/1.63  
% 3.76/1.63  Timing (in seconds)
% 3.76/1.63  ----------------------
% 3.76/1.63  Preprocessing        : 0.35
% 3.76/1.63  Parsing              : 0.18
% 3.76/1.63  CNF conversion       : 0.03
% 3.76/1.63  Main loop            : 0.50
% 3.76/1.63  Inferencing          : 0.17
% 3.76/1.63  Reduction            : 0.17
% 3.76/1.63  Demodulation         : 0.12
% 3.76/1.63  BG Simplification    : 0.03
% 3.76/1.63  Subsumption          : 0.10
% 3.76/1.63  Abstraction          : 0.03
% 3.76/1.63  MUC search           : 0.00
% 3.76/1.63  Cooper               : 0.00
% 3.76/1.63  Total                : 0.89
% 3.76/1.63  Index Insertion      : 0.00
% 3.76/1.63  Index Deletion       : 0.00
% 3.76/1.63  Index Matching       : 0.00
% 3.76/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
