%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 10.90s
% Output     : CNFRefutation 10.90s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 144 expanded)
%              Number of leaves         :   33 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 288 expanded)
%              Number of equality atoms :   25 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_94,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v3_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_46,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_54])).

tff(c_18,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_317,plain,(
    ! [A_106,B_107] :
      ( r1_tarski('#skF_4'(A_106,B_107),B_107)
      | v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_409,plain,(
    ! [A_117] :
      ( r1_tarski('#skF_4'(A_117,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_60,c_317])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_73,plain,(
    ! [A_7] :
      ( A_7 = '#skF_6'
      | ~ r1_tarski(A_7,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_10])).

tff(c_437,plain,(
    ! [A_120] :
      ( '#skF_4'(A_120,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_409,c_73])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_440,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_437,c_42])).

tff(c_443,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_440])).

tff(c_26,plain,(
    ! [A_23] :
      ( v3_pre_topc('#skF_2'(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_2'(A_23),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,(
    ! [A_17,B_81] : k9_subset_1(A_17,B_81,'#skF_6') = k3_xboole_0(B_81,'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_186,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k9_subset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [B_81,A_17] :
      ( m1_subset_1(k3_xboole_0(B_81,'#skF_6'),k1_zfmisc_1(A_17))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_186])).

tff(c_205,plain,(
    ! [B_93,A_94] : m1_subset_1(k3_xboole_0(B_93,'#skF_6'),k1_zfmisc_1(A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_199])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_216,plain,(
    ! [B_95,A_96] : r1_tarski(k3_xboole_0(B_95,'#skF_6'),A_96) ),
    inference(resolution,[status(thm)],[c_205,c_20])).

tff(c_224,plain,(
    ! [B_95] : k3_xboole_0(B_95,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_216,c_73])).

tff(c_227,plain,(
    ! [A_17,B_81] : k9_subset_1(A_17,B_81,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_146])).

tff(c_260,plain,(
    ! [A_100,C_101,B_102] :
      ( k9_subset_1(A_100,C_101,B_102) = k9_subset_1(A_100,B_102,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_268,plain,(
    ! [A_17,B_102] : k9_subset_1(A_17,B_102,'#skF_6') = k9_subset_1(A_17,'#skF_6',B_102) ),
    inference(resolution,[status(thm)],[c_60,c_260])).

tff(c_273,plain,(
    ! [A_17,B_102] : k9_subset_1(A_17,'#skF_6',B_102) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_268])).

tff(c_744,plain,(
    ! [A_147,B_148,D_149] :
      ( k9_subset_1(u1_struct_0(A_147),B_148,D_149) != '#skF_4'(A_147,B_148)
      | ~ v3_pre_topc(D_149,A_147)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(u1_struct_0(A_147)))
      | v2_tex_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_750,plain,(
    ! [A_147,B_102] :
      ( '#skF_4'(A_147,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc(B_102,A_147)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_147)))
      | v2_tex_2('#skF_6',A_147)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_744])).

tff(c_21998,plain,(
    ! [A_666,B_667] :
      ( '#skF_4'(A_666,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc(B_667,A_666)
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_666)))
      | v2_tex_2('#skF_6',A_666)
      | ~ l1_pre_topc(A_666) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_750])).

tff(c_22200,plain,(
    ! [A_670] :
      ( '#skF_4'(A_670,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_2'(A_670),A_670)
      | v2_tex_2('#skF_6',A_670)
      | ~ l1_pre_topc(A_670)
      | ~ v2_pre_topc(A_670) ) ),
    inference(resolution,[status(thm)],[c_28,c_21998])).

tff(c_22205,plain,(
    ! [A_671] :
      ( '#skF_4'(A_671,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_671)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671) ) ),
    inference(resolution,[status(thm)],[c_26,c_22200])).

tff(c_22208,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22205,c_42])).

tff(c_22212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_443,c_22208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.90/4.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/4.35  
% 10.90/4.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/4.35  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 10.90/4.35  
% 10.90/4.35  %Foreground sorts:
% 10.90/4.35  
% 10.90/4.35  
% 10.90/4.35  %Background operators:
% 10.90/4.35  
% 10.90/4.35  
% 10.90/4.35  %Foreground operators:
% 10.90/4.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.90/4.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.90/4.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.90/4.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.90/4.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.90/4.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.90/4.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.90/4.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.90/4.35  tff('#skF_5', type, '#skF_5': $i).
% 10.90/4.35  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.90/4.35  tff('#skF_6', type, '#skF_6': $i).
% 10.90/4.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.90/4.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.90/4.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.90/4.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.90/4.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.90/4.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.90/4.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.90/4.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.90/4.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.90/4.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.90/4.35  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.90/4.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.90/4.35  
% 10.90/4.36  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 10.90/4.36  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.90/4.36  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.90/4.36  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 10.90/4.36  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.90/4.36  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_tops_1)).
% 10.90/4.36  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.90/4.36  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 10.90/4.36  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.90/4.36  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 10.90/4.36  tff(c_50, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.90/4.36  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.90/4.36  tff(c_46, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.90/4.36  tff(c_54, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.90/4.36  tff(c_58, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_46, c_54])).
% 10.90/4.36  tff(c_18, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.90/4.36  tff(c_60, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 10.90/4.36  tff(c_317, plain, (![A_106, B_107]: (r1_tarski('#skF_4'(A_106, B_107), B_107) | v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.90/4.36  tff(c_409, plain, (![A_117]: (r1_tarski('#skF_4'(A_117, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_60, c_317])).
% 10.90/4.36  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.90/4.36  tff(c_73, plain, (![A_7]: (A_7='#skF_6' | ~r1_tarski(A_7, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_10])).
% 10.90/4.36  tff(c_437, plain, (![A_120]: ('#skF_4'(A_120, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_120) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_409, c_73])).
% 10.90/4.36  tff(c_42, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.90/4.36  tff(c_440, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_437, c_42])).
% 10.90/4.36  tff(c_443, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_440])).
% 10.90/4.36  tff(c_26, plain, (![A_23]: (v3_pre_topc('#skF_2'(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.90/4.36  tff(c_28, plain, (![A_23]: (m1_subset_1('#skF_2'(A_23), k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.90/4.36  tff(c_137, plain, (![A_80, B_81, C_82]: (k9_subset_1(A_80, B_81, C_82)=k3_xboole_0(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.90/4.36  tff(c_146, plain, (![A_17, B_81]: (k9_subset_1(A_17, B_81, '#skF_6')=k3_xboole_0(B_81, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_137])).
% 10.90/4.36  tff(c_186, plain, (![A_90, B_91, C_92]: (m1_subset_1(k9_subset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(C_92, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.90/4.36  tff(c_199, plain, (![B_81, A_17]: (m1_subset_1(k3_xboole_0(B_81, '#skF_6'), k1_zfmisc_1(A_17)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_186])).
% 10.90/4.36  tff(c_205, plain, (![B_93, A_94]: (m1_subset_1(k3_xboole_0(B_93, '#skF_6'), k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_199])).
% 10.90/4.36  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.90/4.36  tff(c_216, plain, (![B_95, A_96]: (r1_tarski(k3_xboole_0(B_95, '#skF_6'), A_96))), inference(resolution, [status(thm)], [c_205, c_20])).
% 10.90/4.36  tff(c_224, plain, (![B_95]: (k3_xboole_0(B_95, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_216, c_73])).
% 10.90/4.36  tff(c_227, plain, (![A_17, B_81]: (k9_subset_1(A_17, B_81, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_146])).
% 10.90/4.36  tff(c_260, plain, (![A_100, C_101, B_102]: (k9_subset_1(A_100, C_101, B_102)=k9_subset_1(A_100, B_102, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.90/4.36  tff(c_268, plain, (![A_17, B_102]: (k9_subset_1(A_17, B_102, '#skF_6')=k9_subset_1(A_17, '#skF_6', B_102))), inference(resolution, [status(thm)], [c_60, c_260])).
% 10.90/4.36  tff(c_273, plain, (![A_17, B_102]: (k9_subset_1(A_17, '#skF_6', B_102)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_268])).
% 10.90/4.36  tff(c_744, plain, (![A_147, B_148, D_149]: (k9_subset_1(u1_struct_0(A_147), B_148, D_149)!='#skF_4'(A_147, B_148) | ~v3_pre_topc(D_149, A_147) | ~m1_subset_1(D_149, k1_zfmisc_1(u1_struct_0(A_147))) | v2_tex_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.90/4.36  tff(c_750, plain, (![A_147, B_102]: ('#skF_4'(A_147, '#skF_6')!='#skF_6' | ~v3_pre_topc(B_102, A_147) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_147))) | v2_tex_2('#skF_6', A_147) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(superposition, [status(thm), theory('equality')], [c_273, c_744])).
% 10.90/4.36  tff(c_21998, plain, (![A_666, B_667]: ('#skF_4'(A_666, '#skF_6')!='#skF_6' | ~v3_pre_topc(B_667, A_666) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_666))) | v2_tex_2('#skF_6', A_666) | ~l1_pre_topc(A_666))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_750])).
% 10.90/4.36  tff(c_22200, plain, (![A_670]: ('#skF_4'(A_670, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_2'(A_670), A_670) | v2_tex_2('#skF_6', A_670) | ~l1_pre_topc(A_670) | ~v2_pre_topc(A_670))), inference(resolution, [status(thm)], [c_28, c_21998])).
% 10.90/4.36  tff(c_22205, plain, (![A_671]: ('#skF_4'(A_671, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_671) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671))), inference(resolution, [status(thm)], [c_26, c_22200])).
% 10.90/4.36  tff(c_22208, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22205, c_42])).
% 10.90/4.36  tff(c_22212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_443, c_22208])).
% 10.90/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.90/4.36  
% 10.90/4.36  Inference rules
% 10.90/4.36  ----------------------
% 10.90/4.36  #Ref     : 0
% 10.90/4.36  #Sup     : 5430
% 10.90/4.36  #Fact    : 0
% 10.90/4.36  #Define  : 0
% 10.90/4.36  #Split   : 10
% 10.90/4.36  #Chain   : 0
% 10.90/4.36  #Close   : 0
% 10.90/4.36  
% 10.90/4.36  Ordering : KBO
% 10.90/4.36  
% 10.90/4.36  Simplification rules
% 10.90/4.36  ----------------------
% 10.90/4.36  #Subsume      : 695
% 10.90/4.36  #Demod        : 5059
% 10.90/4.36  #Tautology    : 1930
% 10.90/4.36  #SimpNegUnit  : 35
% 10.90/4.36  #BackRed      : 11
% 10.90/4.36  
% 10.90/4.36  #Partial instantiations: 0
% 10.90/4.36  #Strategies tried      : 1
% 10.90/4.36  
% 10.90/4.36  Timing (in seconds)
% 10.90/4.36  ----------------------
% 10.90/4.36  Preprocessing        : 0.31
% 10.90/4.36  Parsing              : 0.17
% 10.90/4.36  CNF conversion       : 0.02
% 10.90/4.36  Main loop            : 3.22
% 10.90/4.36  Inferencing          : 0.84
% 10.90/4.36  Reduction            : 1.11
% 10.90/4.36  Demodulation         : 0.87
% 10.90/4.36  BG Simplification    : 0.12
% 10.90/4.36  Subsumption          : 0.92
% 10.90/4.36  Abstraction          : 0.16
% 10.90/4.36  MUC search           : 0.00
% 10.90/4.36  Cooper               : 0.00
% 10.90/4.36  Total                : 3.56
% 10.90/4.37  Index Insertion      : 0.00
% 10.90/4.37  Index Deletion       : 0.00
% 10.90/4.37  Index Matching       : 0.00
% 10.90/4.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
