%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 116 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  127 ( 288 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_104,plain,(
    ! [B_74,A_75] :
      ( l1_pre_topc(B_74)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_104])).

tff(c_119,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_110])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_24,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [D_64,B_65] : r2_hidden(D_64,k2_tarski(D_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [D_66,B_67] : ~ v1_xboole_0(k2_tarski(D_66,B_67)) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_82,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_80])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [D_78,B_79,A_80] :
      ( D_78 = B_79
      | D_78 = A_80
      | ~ r2_hidden(D_78,k2_tarski(A_80,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_156,plain,(
    ! [D_81,A_82] :
      ( D_81 = A_82
      | D_81 = A_82
      | ~ r2_hidden(D_81,k1_tarski(A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_164,plain,(
    ! [A_82] :
      ( '#skF_1'(k1_tarski(A_82)) = A_82
      | v1_xboole_0(k1_tarski(A_82)) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_173,plain,(
    ! [A_82] : '#skF_1'(k1_tarski(A_82)) = A_82 ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_164])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_107,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_104])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_107])).

tff(c_30,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_190,plain,(
    ! [A_84,B_85] :
      ( k6_domain_1(A_84,B_85) = k1_tarski(B_85)
      | ~ m1_subset_1(B_85,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_194,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_190])).

tff(c_200,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_34,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_203,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_200,c_34])).

tff(c_206,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_203])).

tff(c_209,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_206])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_209])).

tff(c_215,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_214,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_7') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_282,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k6_domain_1(A_96,B_97),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_290,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_282])).

tff(c_294,plain,
    ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_290])).

tff(c_295,plain,(
    m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_294])).

tff(c_362,plain,(
    ! [C_110,A_111,B_112] :
      ( m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(B_112)))
      | ~ m1_pre_topc(B_112,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_370,plain,(
    ! [A_113] :
      ( m1_subset_1(k1_tarski('#skF_7'),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_pre_topc('#skF_5',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_295,c_362])).

tff(c_28,plain,(
    ! [A_14,C_16,B_15] :
      ( m1_subset_1(A_14,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_381,plain,(
    ! [A_114,A_115] :
      ( m1_subset_1(A_114,u1_struct_0(A_115))
      | ~ r2_hidden(A_114,k1_tarski('#skF_7'))
      | ~ m1_pre_topc('#skF_5',A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_370,c_28])).

tff(c_387,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_1'(k1_tarski('#skF_7')),u1_struct_0(A_115))
      | ~ m1_pre_topc('#skF_5',A_115)
      | ~ l1_pre_topc(A_115)
      | v1_xboole_0(k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4,c_381])).

tff(c_395,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_115))
      | ~ m1_pre_topc('#skF_5',A_115)
      | ~ l1_pre_topc(A_115)
      | v1_xboole_0(k1_tarski('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_387])).

tff(c_398,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_116))
      | ~ m1_pre_topc('#skF_5',A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_395])).

tff(c_42,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_404,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_398,c_42])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_46,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  %$ r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.53/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.53/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.53/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.53/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.32  
% 2.53/1.33  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.53/1.33  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.53/1.33  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.33  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.53/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.53/1.33  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.33  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.53/1.33  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.53/1.33  tff(f_90, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.53/1.33  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.53/1.33  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.53/1.33  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_48, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_104, plain, (![B_74, A_75]: (l1_pre_topc(B_74) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.33  tff(c_110, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_104])).
% 2.53/1.33  tff(c_119, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_110])).
% 2.53/1.33  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_24, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.33  tff(c_72, plain, (![D_64, B_65]: (r2_hidden(D_64, k2_tarski(D_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.33  tff(c_80, plain, (![D_66, B_67]: (~v1_xboole_0(k2_tarski(D_66, B_67)))), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.53/1.33  tff(c_82, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_80])).
% 2.53/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.33  tff(c_128, plain, (![D_78, B_79, A_80]: (D_78=B_79 | D_78=A_80 | ~r2_hidden(D_78, k2_tarski(A_80, B_79)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.33  tff(c_156, plain, (![D_81, A_82]: (D_81=A_82 | D_81=A_82 | ~r2_hidden(D_81, k1_tarski(A_82)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_128])).
% 2.53/1.33  tff(c_164, plain, (![A_82]: ('#skF_1'(k1_tarski(A_82))=A_82 | v1_xboole_0(k1_tarski(A_82)))), inference(resolution, [status(thm)], [c_4, c_156])).
% 2.53/1.33  tff(c_173, plain, (![A_82]: ('#skF_1'(k1_tarski(A_82))=A_82)), inference(negUnitSimplification, [status(thm)], [c_82, c_164])).
% 2.53/1.33  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_107, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_104])).
% 2.53/1.33  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_107])).
% 2.53/1.33  tff(c_30, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.53/1.33  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_190, plain, (![A_84, B_85]: (k6_domain_1(A_84, B_85)=k1_tarski(B_85) | ~m1_subset_1(B_85, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.33  tff(c_194, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_190])).
% 2.53/1.33  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_194])).
% 2.53/1.33  tff(c_34, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.33  tff(c_203, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_200, c_34])).
% 2.53/1.33  tff(c_206, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_203])).
% 2.53/1.33  tff(c_209, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_206])).
% 2.53/1.33  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_209])).
% 2.53/1.33  tff(c_215, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_194])).
% 2.53/1.33  tff(c_214, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_7')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_194])).
% 2.53/1.33  tff(c_282, plain, (![A_96, B_97]: (m1_subset_1(k6_domain_1(A_96, B_97), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.33  tff(c_290, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_282])).
% 2.53/1.33  tff(c_294, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_290])).
% 2.53/1.33  tff(c_295, plain, (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_215, c_294])).
% 2.53/1.33  tff(c_362, plain, (![C_110, A_111, B_112]: (m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(B_112))) | ~m1_pre_topc(B_112, A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.53/1.33  tff(c_370, plain, (![A_113]: (m1_subset_1(k1_tarski('#skF_7'), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_pre_topc('#skF_5', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_295, c_362])).
% 2.53/1.33  tff(c_28, plain, (![A_14, C_16, B_15]: (m1_subset_1(A_14, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.33  tff(c_381, plain, (![A_114, A_115]: (m1_subset_1(A_114, u1_struct_0(A_115)) | ~r2_hidden(A_114, k1_tarski('#skF_7')) | ~m1_pre_topc('#skF_5', A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_370, c_28])).
% 2.53/1.33  tff(c_387, plain, (![A_115]: (m1_subset_1('#skF_1'(k1_tarski('#skF_7')), u1_struct_0(A_115)) | ~m1_pre_topc('#skF_5', A_115) | ~l1_pre_topc(A_115) | v1_xboole_0(k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_4, c_381])).
% 2.53/1.33  tff(c_395, plain, (![A_115]: (m1_subset_1('#skF_7', u1_struct_0(A_115)) | ~m1_pre_topc('#skF_5', A_115) | ~l1_pre_topc(A_115) | v1_xboole_0(k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_387])).
% 2.53/1.33  tff(c_398, plain, (![A_116]: (m1_subset_1('#skF_7', u1_struct_0(A_116)) | ~m1_pre_topc('#skF_5', A_116) | ~l1_pre_topc(A_116))), inference(negUnitSimplification, [status(thm)], [c_82, c_395])).
% 2.53/1.33  tff(c_42, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.53/1.33  tff(c_404, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_398, c_42])).
% 2.53/1.33  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_46, c_404])).
% 2.53/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  Inference rules
% 2.53/1.33  ----------------------
% 2.53/1.33  #Ref     : 0
% 2.53/1.33  #Sup     : 66
% 2.53/1.33  #Fact    : 2
% 2.53/1.33  #Define  : 0
% 2.53/1.33  #Split   : 2
% 2.53/1.33  #Chain   : 0
% 2.53/1.33  #Close   : 0
% 2.53/1.33  
% 2.53/1.33  Ordering : KBO
% 2.53/1.33  
% 2.53/1.33  Simplification rules
% 2.53/1.33  ----------------------
% 2.53/1.33  #Subsume      : 8
% 2.53/1.33  #Demod        : 27
% 2.53/1.33  #Tautology    : 26
% 2.53/1.33  #SimpNegUnit  : 15
% 2.53/1.33  #BackRed      : 0
% 2.53/1.33  
% 2.53/1.33  #Partial instantiations: 0
% 2.53/1.33  #Strategies tried      : 1
% 2.53/1.33  
% 2.53/1.33  Timing (in seconds)
% 2.53/1.33  ----------------------
% 2.53/1.34  Preprocessing        : 0.33
% 2.53/1.34  Parsing              : 0.17
% 2.53/1.34  CNF conversion       : 0.03
% 2.53/1.34  Main loop            : 0.24
% 2.53/1.34  Inferencing          : 0.09
% 2.53/1.34  Reduction            : 0.08
% 2.53/1.34  Demodulation         : 0.05
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.04
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.61
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
