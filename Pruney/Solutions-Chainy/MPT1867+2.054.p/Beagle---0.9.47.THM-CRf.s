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
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 317 expanded)
%              Number of leaves         :   32 ( 123 expanded)
%              Depth                    :   17
%              Number of atoms          :  127 ( 673 expanded)
%              Number of equality atoms :   19 ( 103 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_102,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_70,A_71] :
      ( ~ v1_xboole_0(A_70)
      | ~ r2_hidden(A_71,A_70) ) ),
    inference(resolution,[status(thm)],[c_49,c_102])).

tff(c_131,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_131,c_10])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_147])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_18])).

tff(c_228,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_3'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_255,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_3'(A_92,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_161,c_228])).

tff(c_160,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ r1_tarski(A_6,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_10])).

tff(c_260,plain,(
    ! [A_93] :
      ( '#skF_3'(A_93,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_255,c_160])).

tff(c_263,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_260,c_38])).

tff(c_266,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_263])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_299,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1('#skF_3'(A_97,B_98),k1_zfmisc_1(u1_struct_0(A_97)))
      | v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( v4_pre_topc(B_21,A_19)
      | ~ v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1551,plain,(
    ! [A_212,B_213] :
      ( v4_pre_topc('#skF_3'(A_212,B_213),A_212)
      | ~ v1_xboole_0('#skF_3'(A_212,B_213))
      | ~ v2_pre_topc(A_212)
      | v2_tex_2(B_213,A_212)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_299,c_24])).

tff(c_1574,plain,(
    ! [A_214] :
      ( v4_pre_topc('#skF_3'(A_214,'#skF_5'),A_214)
      | ~ v1_xboole_0('#skF_3'(A_214,'#skF_5'))
      | ~ v2_pre_topc(A_214)
      | v2_tex_2('#skF_5',A_214)
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_161,c_1551])).

tff(c_1577,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_1574])).

tff(c_1579,plain,
    ( v4_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_266,c_1577])).

tff(c_1580,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1579])).

tff(c_80,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,B_61) = B_61
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [A_12,B_61] : k9_subset_1(A_12,B_61,B_61) = B_61 ),
    inference(resolution,[status(thm)],[c_18,c_80])).

tff(c_512,plain,(
    ! [A_127,B_128,D_129] :
      ( k9_subset_1(u1_struct_0(A_127),B_128,D_129) != '#skF_3'(A_127,B_128)
      | ~ v4_pre_topc(D_129,A_127)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3748,plain,(
    ! [A_315,B_316] :
      ( '#skF_3'(A_315,B_316) != B_316
      | ~ v4_pre_topc(B_316,A_315)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | v2_tex_2(B_316,A_315)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_512])).

tff(c_3770,plain,(
    ! [A_315] :
      ( '#skF_3'(A_315,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_315)
      | v2_tex_2('#skF_5',A_315)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_161,c_3748])).

tff(c_3787,plain,(
    ! [A_317] :
      ( '#skF_3'(A_317,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_317)
      | v2_tex_2('#skF_5',A_317)
      | ~ l1_pre_topc(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3770])).

tff(c_3790,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1580,c_3787])).

tff(c_3796,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_266,c_3790])).

tff(c_3798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.40/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/1.98  
% 5.40/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/1.98  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 5.40/1.98  
% 5.40/1.98  %Foreground sorts:
% 5.40/1.98  
% 5.40/1.98  
% 5.40/1.98  %Background operators:
% 5.40/1.98  
% 5.40/1.98  
% 5.40/1.98  %Foreground operators:
% 5.40/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.40/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.40/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.40/1.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.40/1.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.40/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.40/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.40/1.98  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.40/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.40/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.40/1.98  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.40/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.40/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/1.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.40/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.40/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.40/1.98  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.40/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.40/1.98  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.40/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.40/1.98  
% 5.40/2.00  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 5.40/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.40/2.00  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.40/2.00  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.40/2.00  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.40/2.00  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.40/2.00  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.40/2.00  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 5.40/2.00  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 5.40/2.00  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 5.40/2.00  tff(c_38, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.40/2.00  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.40/2.00  tff(c_42, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.40/2.00  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.00  tff(c_12, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.40/2.00  tff(c_14, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.40/2.00  tff(c_49, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 5.40/2.00  tff(c_102, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.40/2.00  tff(c_126, plain, (![A_70, A_71]: (~v1_xboole_0(A_70) | ~r2_hidden(A_71, A_70))), inference(resolution, [status(thm)], [c_49, c_102])).
% 5.40/2.00  tff(c_131, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_6, c_126])).
% 5.40/2.00  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.40/2.00  tff(c_147, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_131, c_10])).
% 5.40/2.00  tff(c_156, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_147])).
% 5.40/2.00  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.40/2.00  tff(c_161, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_18])).
% 5.40/2.00  tff(c_228, plain, (![A_88, B_89]: (r1_tarski('#skF_3'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.40/2.00  tff(c_255, plain, (![A_92]: (r1_tarski('#skF_3'(A_92, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_161, c_228])).
% 5.40/2.00  tff(c_160, plain, (![A_6]: (A_6='#skF_5' | ~r1_tarski(A_6, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_10])).
% 5.40/2.00  tff(c_260, plain, (![A_93]: ('#skF_3'(A_93, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_255, c_160])).
% 5.40/2.00  tff(c_263, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_260, c_38])).
% 5.40/2.00  tff(c_266, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_263])).
% 5.40/2.00  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.40/2.00  tff(c_299, plain, (![A_97, B_98]: (m1_subset_1('#skF_3'(A_97, B_98), k1_zfmisc_1(u1_struct_0(A_97))) | v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.40/2.00  tff(c_24, plain, (![B_21, A_19]: (v4_pre_topc(B_21, A_19) | ~v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.40/2.00  tff(c_1551, plain, (![A_212, B_213]: (v4_pre_topc('#skF_3'(A_212, B_213), A_212) | ~v1_xboole_0('#skF_3'(A_212, B_213)) | ~v2_pre_topc(A_212) | v2_tex_2(B_213, A_212) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_299, c_24])).
% 5.40/2.00  tff(c_1574, plain, (![A_214]: (v4_pre_topc('#skF_3'(A_214, '#skF_5'), A_214) | ~v1_xboole_0('#skF_3'(A_214, '#skF_5')) | ~v2_pre_topc(A_214) | v2_tex_2('#skF_5', A_214) | ~l1_pre_topc(A_214))), inference(resolution, [status(thm)], [c_161, c_1551])).
% 5.40/2.00  tff(c_1577, plain, (v4_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_266, c_1574])).
% 5.40/2.00  tff(c_1579, plain, (v4_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_266, c_1577])).
% 5.40/2.00  tff(c_1580, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_1579])).
% 5.40/2.00  tff(c_80, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, B_61)=B_61 | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.40/2.00  tff(c_88, plain, (![A_12, B_61]: (k9_subset_1(A_12, B_61, B_61)=B_61)), inference(resolution, [status(thm)], [c_18, c_80])).
% 5.40/2.00  tff(c_512, plain, (![A_127, B_128, D_129]: (k9_subset_1(u1_struct_0(A_127), B_128, D_129)!='#skF_3'(A_127, B_128) | ~v4_pre_topc(D_129, A_127) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.40/2.00  tff(c_3748, plain, (![A_315, B_316]: ('#skF_3'(A_315, B_316)!=B_316 | ~v4_pre_topc(B_316, A_315) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | v2_tex_2(B_316, A_315) | ~m1_subset_1(B_316, k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(superposition, [status(thm), theory('equality')], [c_88, c_512])).
% 5.40/2.00  tff(c_3770, plain, (![A_315]: ('#skF_3'(A_315, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_315) | v2_tex_2('#skF_5', A_315) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_315))) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_161, c_3748])).
% 5.40/2.00  tff(c_3787, plain, (![A_317]: ('#skF_3'(A_317, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_317) | v2_tex_2('#skF_5', A_317) | ~l1_pre_topc(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3770])).
% 5.40/2.00  tff(c_3790, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1580, c_3787])).
% 5.40/2.00  tff(c_3796, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_266, c_3790])).
% 5.40/2.00  tff(c_3798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_3796])).
% 5.40/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.40/2.00  
% 5.40/2.00  Inference rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Ref     : 0
% 5.40/2.00  #Sup     : 965
% 5.40/2.00  #Fact    : 4
% 5.40/2.00  #Define  : 0
% 5.40/2.00  #Split   : 4
% 5.40/2.00  #Chain   : 0
% 5.40/2.00  #Close   : 0
% 5.40/2.00  
% 5.40/2.00  Ordering : KBO
% 5.40/2.00  
% 5.40/2.00  Simplification rules
% 5.40/2.00  ----------------------
% 5.40/2.00  #Subsume      : 542
% 5.40/2.00  #Demod        : 117
% 5.40/2.00  #Tautology    : 237
% 5.40/2.00  #SimpNegUnit  : 17
% 5.40/2.00  #BackRed      : 8
% 5.40/2.00  
% 5.40/2.00  #Partial instantiations: 0
% 5.40/2.00  #Strategies tried      : 1
% 5.40/2.00  
% 5.40/2.00  Timing (in seconds)
% 5.40/2.00  ----------------------
% 5.40/2.00  Preprocessing        : 0.29
% 5.40/2.00  Parsing              : 0.16
% 5.40/2.00  CNF conversion       : 0.02
% 5.40/2.00  Main loop            : 0.95
% 5.40/2.00  Inferencing          : 0.28
% 5.40/2.00  Reduction            : 0.24
% 5.40/2.00  Demodulation         : 0.16
% 5.40/2.00  BG Simplification    : 0.03
% 5.40/2.00  Subsumption          : 0.34
% 5.40/2.00  Abstraction          : 0.04
% 5.40/2.00  MUC search           : 0.00
% 5.40/2.00  Cooper               : 0.00
% 5.40/2.00  Total                : 1.28
% 5.40/2.00  Index Insertion      : 0.00
% 5.40/2.00  Index Deletion       : 0.00
% 5.40/2.00  Index Matching       : 0.00
% 5.40/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
