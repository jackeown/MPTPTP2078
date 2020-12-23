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
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 212 expanded)
%              Number of leaves         :   32 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  128 ( 473 expanded)
%              Number of equality atoms :   20 (  78 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_103,axiom,(
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

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_44,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_59,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ! [A_13] : m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_306,plain,(
    ! [A_101,B_102] :
      ( r1_tarski('#skF_3'(A_101,B_102),B_102)
      | v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_420,plain,(
    ! [A_114] :
      ( r1_tarski('#skF_3'(A_114,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_70,c_306])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_112,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ r1_tarski(A_6,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_71,c_112])).

tff(c_436,plain,(
    ! [A_115] :
      ( '#skF_3'(A_115,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_420,c_117])).

tff(c_439,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_436,c_44])).

tff(c_442,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_439])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_402,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1('#skF_3'(A_112,B_113),k1_zfmisc_1(u1_struct_0(A_112)))
      | v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [B_23,A_21] :
      ( v3_pre_topc(B_23,A_21)
      | ~ v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2299,plain,(
    ! [A_244,B_245] :
      ( v3_pre_topc('#skF_3'(A_244,B_245),A_244)
      | ~ v1_xboole_0('#skF_3'(A_244,B_245))
      | ~ v2_pre_topc(A_244)
      | v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_402,c_30])).

tff(c_2342,plain,(
    ! [A_246] :
      ( v3_pre_topc('#skF_3'(A_246,'#skF_5'),A_246)
      | ~ v1_xboole_0('#skF_3'(A_246,'#skF_5'))
      | ~ v2_pre_topc(A_246)
      | v2_tex_2('#skF_5',A_246)
      | ~ l1_pre_topc(A_246) ) ),
    inference(resolution,[status(thm)],[c_70,c_2299])).

tff(c_2345,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_2342])).

tff(c_2347,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_48,c_442,c_2345])).

tff(c_2348,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2347])).

tff(c_152,plain,(
    ! [A_76,B_77,C_78] :
      ( k9_subset_1(A_76,B_77,C_78) = k3_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    ! [A_13,B_77] : k9_subset_1(A_13,B_77,'#skF_5') = k3_xboole_0(B_77,'#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_152])).

tff(c_190,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k9_subset_1(A_86,B_87,C_88),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_200,plain,(
    ! [B_77,A_13] :
      ( m1_subset_1(k3_xboole_0(B_77,'#skF_5'),k1_zfmisc_1(A_13))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_190])).

tff(c_206,plain,(
    ! [B_89,A_90] : m1_subset_1(k3_xboole_0(B_89,'#skF_5'),k1_zfmisc_1(A_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_200])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    ! [B_91,A_92] : r1_tarski(k3_xboole_0(B_91,'#skF_5'),A_92) ),
    inference(resolution,[status(thm)],[c_206,c_22])).

tff(c_231,plain,(
    ! [B_91] : k3_xboole_0(B_91,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_217,c_117])).

tff(c_236,plain,(
    ! [A_13,B_77] : k9_subset_1(A_13,B_77,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_158])).

tff(c_552,plain,(
    ! [A_122,B_123,D_124] :
      ( k9_subset_1(u1_struct_0(A_122),B_123,D_124) != '#skF_3'(A_122,B_123)
      | ~ v3_pre_topc(D_124,A_122)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | v2_tex_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_558,plain,(
    ! [A_122,B_77] :
      ( '#skF_3'(A_122,B_77) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_122)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_122)))
      | v2_tex_2(B_77,A_122)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_552])).

tff(c_2577,plain,(
    ! [A_263,B_264] :
      ( '#skF_3'(A_263,B_264) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_263)
      | v2_tex_2(B_264,A_263)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_558])).

tff(c_2636,plain,(
    ! [A_265] :
      ( '#skF_3'(A_265,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_265)
      | v2_tex_2('#skF_5',A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_70,c_2577])).

tff(c_2639,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2348,c_2636])).

tff(c_2645,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_442,c_2639])).

tff(c_2647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:37:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.82  
% 4.46/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.82  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.46/1.82  
% 4.46/1.82  %Foreground sorts:
% 4.46/1.82  
% 4.46/1.82  
% 4.46/1.82  %Background operators:
% 4.46/1.82  
% 4.46/1.82  
% 4.46/1.82  %Foreground operators:
% 4.46/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.46/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.46/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.46/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.46/1.82  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.46/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.46/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.46/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.46/1.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.46/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.82  
% 4.71/1.83  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 4.71/1.83  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.71/1.83  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.71/1.83  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 4.71/1.83  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.71/1.83  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.71/1.83  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 4.71/1.83  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.71/1.83  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 4.71/1.83  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.71/1.83  tff(c_44, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.83  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.83  tff(c_48, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.83  tff(c_59, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.71/1.83  tff(c_68, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_59])).
% 4.71/1.83  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.71/1.83  tff(c_70, plain, (![A_13]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 4.71/1.83  tff(c_306, plain, (![A_101, B_102]: (r1_tarski('#skF_3'(A_101, B_102), B_102) | v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.71/1.83  tff(c_420, plain, (![A_114]: (r1_tarski('#skF_3'(A_114, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_114) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_70, c_306])).
% 4.71/1.83  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.71/1.83  tff(c_71, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14])).
% 4.71/1.83  tff(c_112, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.71/1.83  tff(c_117, plain, (![A_6]: (A_6='#skF_5' | ~r1_tarski(A_6, '#skF_5'))), inference(resolution, [status(thm)], [c_71, c_112])).
% 4.71/1.83  tff(c_436, plain, (![A_115]: ('#skF_3'(A_115, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_420, c_117])).
% 4.71/1.83  tff(c_439, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_436, c_44])).
% 4.71/1.83  tff(c_442, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_439])).
% 4.71/1.83  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.83  tff(c_402, plain, (![A_112, B_113]: (m1_subset_1('#skF_3'(A_112, B_113), k1_zfmisc_1(u1_struct_0(A_112))) | v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.71/1.83  tff(c_30, plain, (![B_23, A_21]: (v3_pre_topc(B_23, A_21) | ~v1_xboole_0(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.71/1.83  tff(c_2299, plain, (![A_244, B_245]: (v3_pre_topc('#skF_3'(A_244, B_245), A_244) | ~v1_xboole_0('#skF_3'(A_244, B_245)) | ~v2_pre_topc(A_244) | v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_402, c_30])).
% 4.71/1.83  tff(c_2342, plain, (![A_246]: (v3_pre_topc('#skF_3'(A_246, '#skF_5'), A_246) | ~v1_xboole_0('#skF_3'(A_246, '#skF_5')) | ~v2_pre_topc(A_246) | v2_tex_2('#skF_5', A_246) | ~l1_pre_topc(A_246))), inference(resolution, [status(thm)], [c_70, c_2299])).
% 4.71/1.83  tff(c_2345, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_442, c_2342])).
% 4.71/1.83  tff(c_2347, plain, (v3_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_48, c_442, c_2345])).
% 4.71/1.83  tff(c_2348, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_2347])).
% 4.71/1.83  tff(c_152, plain, (![A_76, B_77, C_78]: (k9_subset_1(A_76, B_77, C_78)=k3_xboole_0(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.83  tff(c_158, plain, (![A_13, B_77]: (k9_subset_1(A_13, B_77, '#skF_5')=k3_xboole_0(B_77, '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_152])).
% 4.71/1.83  tff(c_190, plain, (![A_86, B_87, C_88]: (m1_subset_1(k9_subset_1(A_86, B_87, C_88), k1_zfmisc_1(A_86)) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.71/1.83  tff(c_200, plain, (![B_77, A_13]: (m1_subset_1(k3_xboole_0(B_77, '#skF_5'), k1_zfmisc_1(A_13)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_190])).
% 4.71/1.83  tff(c_206, plain, (![B_89, A_90]: (m1_subset_1(k3_xboole_0(B_89, '#skF_5'), k1_zfmisc_1(A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_200])).
% 4.71/1.83  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.71/1.83  tff(c_217, plain, (![B_91, A_92]: (r1_tarski(k3_xboole_0(B_91, '#skF_5'), A_92))), inference(resolution, [status(thm)], [c_206, c_22])).
% 4.71/1.83  tff(c_231, plain, (![B_91]: (k3_xboole_0(B_91, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_217, c_117])).
% 4.71/1.83  tff(c_236, plain, (![A_13, B_77]: (k9_subset_1(A_13, B_77, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_158])).
% 4.71/1.83  tff(c_552, plain, (![A_122, B_123, D_124]: (k9_subset_1(u1_struct_0(A_122), B_123, D_124)!='#skF_3'(A_122, B_123) | ~v3_pre_topc(D_124, A_122) | ~m1_subset_1(D_124, k1_zfmisc_1(u1_struct_0(A_122))) | v2_tex_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.71/1.83  tff(c_558, plain, (![A_122, B_77]: ('#skF_3'(A_122, B_77)!='#skF_5' | ~v3_pre_topc('#skF_5', A_122) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_122))) | v2_tex_2(B_77, A_122) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(superposition, [status(thm), theory('equality')], [c_236, c_552])).
% 4.71/1.83  tff(c_2577, plain, (![A_263, B_264]: ('#skF_3'(A_263, B_264)!='#skF_5' | ~v3_pre_topc('#skF_5', A_263) | v2_tex_2(B_264, A_263) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_558])).
% 4.71/1.83  tff(c_2636, plain, (![A_265]: ('#skF_3'(A_265, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_265) | v2_tex_2('#skF_5', A_265) | ~l1_pre_topc(A_265))), inference(resolution, [status(thm)], [c_70, c_2577])).
% 4.71/1.83  tff(c_2639, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2348, c_2636])).
% 4.71/1.83  tff(c_2645, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_442, c_2639])).
% 4.71/1.83  tff(c_2647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2645])).
% 4.71/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.83  
% 4.71/1.83  Inference rules
% 4.71/1.83  ----------------------
% 4.71/1.83  #Ref     : 0
% 4.71/1.83  #Sup     : 595
% 4.71/1.83  #Fact    : 0
% 4.71/1.83  #Define  : 0
% 4.71/1.83  #Split   : 1
% 4.71/1.83  #Chain   : 0
% 4.71/1.84  #Close   : 0
% 4.71/1.84  
% 4.71/1.84  Ordering : KBO
% 4.71/1.84  
% 4.71/1.84  Simplification rules
% 4.71/1.84  ----------------------
% 4.71/1.84  #Subsume      : 89
% 4.71/1.84  #Demod        : 491
% 4.71/1.84  #Tautology    : 205
% 4.71/1.84  #SimpNegUnit  : 16
% 4.71/1.84  #BackRed      : 9
% 4.71/1.84  
% 4.71/1.84  #Partial instantiations: 0
% 4.71/1.84  #Strategies tried      : 1
% 4.71/1.84  
% 4.71/1.84  Timing (in seconds)
% 4.71/1.84  ----------------------
% 4.71/1.84  Preprocessing        : 0.31
% 4.71/1.84  Parsing              : 0.15
% 4.71/1.84  CNF conversion       : 0.02
% 4.71/1.84  Main loop            : 0.73
% 4.71/1.84  Inferencing          : 0.24
% 4.71/1.84  Reduction            : 0.24
% 4.71/1.84  Demodulation         : 0.17
% 4.71/1.84  BG Simplification    : 0.04
% 4.71/1.84  Subsumption          : 0.16
% 4.71/1.84  Abstraction          : 0.05
% 4.71/1.84  MUC search           : 0.00
% 4.71/1.84  Cooper               : 0.00
% 4.71/1.84  Total                : 1.07
% 4.71/1.84  Index Insertion      : 0.00
% 4.71/1.84  Index Deletion       : 0.00
% 4.71/1.84  Index Matching       : 0.00
% 4.71/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
