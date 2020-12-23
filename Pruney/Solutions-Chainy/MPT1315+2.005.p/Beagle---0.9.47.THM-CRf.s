%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:02 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 368 expanded)
%              Number of leaves         :   35 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 (1058 expanded)
%              Number of equality atoms :   26 ( 135 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_124,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_53,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_106,axiom,(
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

tff(c_56,plain,(
    ~ v4_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_64,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_108,plain,(
    ! [B_98,A_99] :
      ( l1_pre_topc(B_98)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_111,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_114,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_111])).

tff(c_202,plain,(
    ! [A_116,B_117] :
      ( m1_pre_topc(k1_pre_topc(A_116,B_117),A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_204,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_202])).

tff(c_209,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_204])).

tff(c_46,plain,(
    ! [B_62,A_60] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_215,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_209,c_46])).

tff(c_218,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_215])).

tff(c_116,plain,(
    ! [A_102,B_103] :
      ( v1_pre_topc(k1_pre_topc(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_125,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_119])).

tff(c_361,plain,(
    ! [A_143,B_144] :
      ( k2_struct_0(k1_pre_topc(A_143,B_144)) = B_144
      | ~ m1_pre_topc(k1_pre_topc(A_143,B_144),A_143)
      | ~ v1_pre_topc(k1_pre_topc(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_365,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_209,c_361])).

tff(c_371,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_60,c_125,c_365])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k2_struct_0(B_107),k2_struct_0(A_108))
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(B_107)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [B_120,A_121] :
      ( k3_xboole_0(k2_struct_0(B_120),k2_struct_0(A_121)) = k2_struct_0(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(B_120)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_232,plain,(
    ! [A_121,B_120] :
      ( k3_xboole_0(k2_struct_0(A_121),k2_struct_0(B_120)) = k2_struct_0(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(B_120)
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_2])).

tff(c_386,plain,(
    ! [A_121] :
      ( k3_xboole_0(k2_struct_0(A_121),'#skF_8') = k2_struct_0(k1_pre_topc('#skF_7','#skF_8'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_121)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_232])).

tff(c_517,plain,(
    ! [A_150] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_150)) = '#skF_8'
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_371,c_2,c_386])).

tff(c_520,plain,
    ( k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8'
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_209,c_517])).

tff(c_523,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_520])).

tff(c_129,plain,(
    ! [A_104,B_105,C_106] :
      ( k9_subset_1(A_104,B_105,C_106) = k3_xboole_0(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [B_105] : k9_subset_1(u1_struct_0('#skF_7'),B_105,'#skF_8') = k3_xboole_0(B_105,'#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_129])).

tff(c_159,plain,(
    ! [A_111,C_112,B_113] :
      ( k9_subset_1(A_111,C_112,B_113) = k9_subset_1(A_111,B_113,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [B_113] : k9_subset_1(u1_struct_0('#skF_7'),B_113,'#skF_8') = k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_113) ),
    inference(resolution,[status(thm)],[c_60,c_159])).

tff(c_165,plain,(
    ! [B_113] : k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_113) = k3_xboole_0(B_113,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_161])).

tff(c_58,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_62,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_69,plain,(
    v4_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_66])).

tff(c_1143,plain,(
    ! [B_223,D_224,A_225] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_223),D_224,k2_struct_0(B_223)),B_223)
      | ~ v4_pre_topc(D_224,A_225)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_223),D_224,k2_struct_0(B_223)),k1_zfmisc_1(u1_struct_0(B_223)))
      | ~ m1_pre_topc(B_223,A_225)
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1155,plain,(
    ! [B_223] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_223),'#skF_8',k2_struct_0(B_223)),B_223)
      | ~ v4_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_223),'#skF_8',k2_struct_0(B_223)),k1_zfmisc_1(u1_struct_0(B_223)))
      | ~ m1_pre_topc(B_223,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_1143])).

tff(c_1166,plain,(
    ! [B_226] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_226),'#skF_8',k2_struct_0(B_226)),B_226)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_226),'#skF_8',k2_struct_0(B_226)),k1_zfmisc_1(u1_struct_0(B_226)))
      | ~ m1_pre_topc(B_226,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69,c_1155])).

tff(c_1183,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1166])).

tff(c_1190,plain,(
    v4_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_523,c_2,c_523,c_2,c_165,c_1183])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:43:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.72  
% 4.10/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.72  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 4.10/1.72  
% 4.10/1.72  %Foreground sorts:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Background operators:
% 4.10/1.72  
% 4.10/1.72  
% 4.10/1.72  %Foreground operators:
% 4.10/1.72  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 4.10/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.10/1.72  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.10/1.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.10/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.10/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.10/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.10/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.10/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.10/1.72  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.10/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.10/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.10/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.10/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.10/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.10/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.10/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.10/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.72  
% 4.10/1.74  tff(f_124, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 4.10/1.74  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.10/1.74  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 4.10/1.74  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 4.10/1.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.10/1.74  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 4.10/1.74  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.10/1.74  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.10/1.74  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.10/1.74  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 4.10/1.74  tff(c_56, plain, (~v4_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_64, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_108, plain, (![B_98, A_99]: (l1_pre_topc(B_98) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.10/1.74  tff(c_111, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_108])).
% 4.10/1.74  tff(c_114, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_111])).
% 4.10/1.74  tff(c_202, plain, (![A_116, B_117]: (m1_pre_topc(k1_pre_topc(A_116, B_117), A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.10/1.74  tff(c_204, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_60, c_202])).
% 4.10/1.74  tff(c_209, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_204])).
% 4.10/1.74  tff(c_46, plain, (![B_62, A_60]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.10/1.74  tff(c_215, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_209, c_46])).
% 4.10/1.74  tff(c_218, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_215])).
% 4.10/1.74  tff(c_116, plain, (![A_102, B_103]: (v1_pre_topc(k1_pre_topc(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.10/1.74  tff(c_119, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_60, c_116])).
% 4.10/1.74  tff(c_125, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_119])).
% 4.10/1.74  tff(c_361, plain, (![A_143, B_144]: (k2_struct_0(k1_pre_topc(A_143, B_144))=B_144 | ~m1_pre_topc(k1_pre_topc(A_143, B_144), A_143) | ~v1_pre_topc(k1_pre_topc(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.10/1.74  tff(c_365, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_209, c_361])).
% 4.10/1.74  tff(c_371, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_60, c_125, c_365])).
% 4.10/1.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.10/1.74  tff(c_136, plain, (![B_107, A_108]: (r1_tarski(k2_struct_0(B_107), k2_struct_0(A_108)) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(B_107) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.74  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.10/1.74  tff(c_226, plain, (![B_120, A_121]: (k3_xboole_0(k2_struct_0(B_120), k2_struct_0(A_121))=k2_struct_0(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(B_120) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_136, c_4])).
% 4.10/1.74  tff(c_232, plain, (![A_121, B_120]: (k3_xboole_0(k2_struct_0(A_121), k2_struct_0(B_120))=k2_struct_0(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(B_120) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_226, c_2])).
% 4.10/1.74  tff(c_386, plain, (![A_121]: (k3_xboole_0(k2_struct_0(A_121), '#skF_8')=k2_struct_0(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_121) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_121))), inference(superposition, [status(thm), theory('equality')], [c_371, c_232])).
% 4.10/1.74  tff(c_517, plain, (![A_150]: (k3_xboole_0('#skF_8', k2_struct_0(A_150))='#skF_8' | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_150) | ~l1_pre_topc(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_371, c_2, c_386])).
% 4.10/1.74  tff(c_520, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8' | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_209, c_517])).
% 4.10/1.74  tff(c_523, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_520])).
% 4.10/1.74  tff(c_129, plain, (![A_104, B_105, C_106]: (k9_subset_1(A_104, B_105, C_106)=k3_xboole_0(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.74  tff(c_134, plain, (![B_105]: (k9_subset_1(u1_struct_0('#skF_7'), B_105, '#skF_8')=k3_xboole_0(B_105, '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_129])).
% 4.10/1.74  tff(c_159, plain, (![A_111, C_112, B_113]: (k9_subset_1(A_111, C_112, B_113)=k9_subset_1(A_111, B_113, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.10/1.74  tff(c_161, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_7'), B_113, '#skF_8')=k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_113))), inference(resolution, [status(thm)], [c_60, c_159])).
% 4.10/1.74  tff(c_165, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_113)=k3_xboole_0(B_113, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_161])).
% 4.10/1.74  tff(c_58, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_62, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_69, plain, (v4_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62])).
% 4.10/1.74  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.10/1.74  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_66])).
% 4.10/1.74  tff(c_1143, plain, (![B_223, D_224, A_225]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_223), D_224, k2_struct_0(B_223)), B_223) | ~v4_pre_topc(D_224, A_225) | ~m1_subset_1(D_224, k1_zfmisc_1(u1_struct_0(A_225))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_223), D_224, k2_struct_0(B_223)), k1_zfmisc_1(u1_struct_0(B_223))) | ~m1_pre_topc(B_223, A_225) | ~l1_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.10/1.74  tff(c_1155, plain, (![B_223]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_223), '#skF_8', k2_struct_0(B_223)), B_223) | ~v4_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0(B_223), '#skF_8', k2_struct_0(B_223)), k1_zfmisc_1(u1_struct_0(B_223))) | ~m1_pre_topc(B_223, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_1143])).
% 4.10/1.74  tff(c_1166, plain, (![B_226]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_226), '#skF_8', k2_struct_0(B_226)), B_226) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_226), '#skF_8', k2_struct_0(B_226)), k1_zfmisc_1(u1_struct_0(B_226))) | ~m1_pre_topc(B_226, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69, c_1155])).
% 4.10/1.74  tff(c_1183, plain, (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_165, c_1166])).
% 4.10/1.74  tff(c_1190, plain, (v4_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_523, c_2, c_523, c_2, c_165, c_1183])).
% 4.10/1.74  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1190])).
% 4.10/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.74  
% 4.10/1.74  Inference rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Ref     : 0
% 4.10/1.74  #Sup     : 256
% 4.10/1.74  #Fact    : 0
% 4.10/1.74  #Define  : 0
% 4.10/1.74  #Split   : 11
% 4.10/1.74  #Chain   : 0
% 4.10/1.74  #Close   : 0
% 4.10/1.74  
% 4.10/1.74  Ordering : KBO
% 4.10/1.74  
% 4.10/1.74  Simplification rules
% 4.10/1.74  ----------------------
% 4.10/1.74  #Subsume      : 37
% 4.10/1.74  #Demod        : 155
% 4.10/1.74  #Tautology    : 58
% 4.10/1.74  #SimpNegUnit  : 7
% 4.10/1.74  #BackRed      : 0
% 4.10/1.74  
% 4.10/1.74  #Partial instantiations: 0
% 4.10/1.74  #Strategies tried      : 1
% 4.10/1.74  
% 4.10/1.74  Timing (in seconds)
% 4.10/1.74  ----------------------
% 4.10/1.74  Preprocessing        : 0.37
% 4.10/1.74  Parsing              : 0.18
% 4.10/1.74  CNF conversion       : 0.03
% 4.10/1.74  Main loop            : 0.61
% 4.10/1.74  Inferencing          : 0.21
% 4.10/1.74  Reduction            : 0.20
% 4.10/1.74  Demodulation         : 0.15
% 4.10/1.74  BG Simplification    : 0.03
% 4.10/1.74  Subsumption          : 0.13
% 4.10/1.74  Abstraction          : 0.03
% 4.10/1.74  MUC search           : 0.00
% 4.10/1.74  Cooper               : 0.00
% 4.10/1.74  Total                : 1.01
% 4.10/1.74  Index Insertion      : 0.00
% 4.10/1.74  Index Deletion       : 0.00
% 4.10/1.74  Index Matching       : 0.00
% 4.10/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
