%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 172 expanded)
%              Number of leaves         :   29 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 398 expanded)
%              Number of equality atoms :   21 (  70 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_8,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_8])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_106,plain,(
    ! [A_60,B_61] :
      ( r1_tarski('#skF_2'(A_60,B_61),B_61)
      | v2_tex_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_63] :
      ( r1_tarski('#skF_2'(A_63,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_53,c_106])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k2_xboole_0(A_2,B_3) = B_3
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_115,plain,(
    ! [A_63] :
      ( k2_xboole_0('#skF_2'(A_63,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_118,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_115])).

tff(c_121,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_30])).

tff(c_124,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_140,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1('#skF_2'(A_65,B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [B_14,A_12] :
      ( v3_pre_topc(B_14,A_12)
      | ~ v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    ! [A_70,B_71] :
      ( v3_pre_topc('#skF_2'(A_70,B_71),A_70)
      | ~ v1_xboole_0('#skF_2'(A_70,B_71))
      | ~ v2_pre_topc(A_70)
      | v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_140,c_16])).

tff(c_171,plain,(
    ! [A_72] :
      ( v3_pre_topc('#skF_2'(A_72,'#skF_4'),A_72)
      | ~ v1_xboole_0('#skF_2'(A_72,'#skF_4'))
      | ~ v2_pre_topc(A_72)
      | v2_tex_2('#skF_4',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_53,c_163])).

tff(c_174,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_171])).

tff(c_176,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_34,c_124,c_174])).

tff(c_177,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_176])).

tff(c_79,plain,(
    ! [A_48,B_49,C_50] :
      ( k9_subset_1(A_48,B_49,B_49) = B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_8,B_49] : k9_subset_1(A_8,B_49,B_49) = B_49 ),
    inference(resolution,[status(thm)],[c_53,c_79])).

tff(c_214,plain,(
    ! [A_81,B_82,D_83] :
      ( k9_subset_1(u1_struct_0(A_81),B_82,D_83) != '#skF_2'(A_81,B_82)
      | ~ v3_pre_topc(D_83,A_81)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,(
    ! [A_87,B_88] :
      ( '#skF_2'(A_87,B_88) != B_88
      | ~ v3_pre_topc(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_214])).

tff(c_245,plain,(
    ! [A_87] :
      ( '#skF_2'(A_87,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_87)
      | v2_tex_2('#skF_4',A_87)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_53,c_238])).

tff(c_251,plain,(
    ! [A_89] :
      ( '#skF_2'(A_89,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_89)
      | v2_tex_2('#skF_4',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_245])).

tff(c_254,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_251])).

tff(c_260,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_124,c_254])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.26  
% 2.29/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.26  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.29/1.26  
% 2.29/1.26  %Foreground sorts:
% 2.29/1.26  
% 2.29/1.26  
% 2.29/1.26  %Background operators:
% 2.29/1.26  
% 2.29/1.26  
% 2.29/1.26  %Foreground operators:
% 2.29/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.29/1.26  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.26  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.29/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.29/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.26  
% 2.29/1.28  tff(f_95, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.29/1.28  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.29/1.28  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.29/1.28  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.29/1.28  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.29/1.28  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.29/1.28  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.29/1.28  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.29/1.28  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.29/1.28  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.29/1.28  tff(c_34, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.29/1.28  tff(c_42, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.29/1.28  tff(c_51, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.29/1.28  tff(c_8, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.29/1.28  tff(c_60, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_8])).
% 2.29/1.28  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.29/1.28  tff(c_53, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_12])).
% 2.29/1.28  tff(c_106, plain, (![A_60, B_61]: (r1_tarski('#skF_2'(A_60, B_61), B_61) | v2_tex_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.28  tff(c_112, plain, (![A_63]: (r1_tarski('#skF_2'(A_63, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_53, c_106])).
% 2.29/1.28  tff(c_6, plain, (![A_2, B_3]: (k2_xboole_0(A_2, B_3)=B_3 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.29/1.28  tff(c_115, plain, (![A_63]: (k2_xboole_0('#skF_2'(A_63, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_112, c_6])).
% 2.29/1.28  tff(c_118, plain, (![A_64]: ('#skF_2'(A_64, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_64) | ~l1_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_115])).
% 2.29/1.28  tff(c_121, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_118, c_30])).
% 2.29/1.28  tff(c_124, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 2.29/1.28  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.29/1.28  tff(c_140, plain, (![A_65, B_66]: (m1_subset_1('#skF_2'(A_65, B_66), k1_zfmisc_1(u1_struct_0(A_65))) | v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.28  tff(c_16, plain, (![B_14, A_12]: (v3_pre_topc(B_14, A_12) | ~v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.29/1.28  tff(c_163, plain, (![A_70, B_71]: (v3_pre_topc('#skF_2'(A_70, B_71), A_70) | ~v1_xboole_0('#skF_2'(A_70, B_71)) | ~v2_pre_topc(A_70) | v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_140, c_16])).
% 2.29/1.28  tff(c_171, plain, (![A_72]: (v3_pre_topc('#skF_2'(A_72, '#skF_4'), A_72) | ~v1_xboole_0('#skF_2'(A_72, '#skF_4')) | ~v2_pre_topc(A_72) | v2_tex_2('#skF_4', A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_53, c_163])).
% 2.29/1.28  tff(c_174, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_171])).
% 2.29/1.28  tff(c_176, plain, (v3_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_34, c_124, c_174])).
% 2.29/1.28  tff(c_177, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_176])).
% 2.29/1.28  tff(c_79, plain, (![A_48, B_49, C_50]: (k9_subset_1(A_48, B_49, B_49)=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.29/1.28  tff(c_82, plain, (![A_8, B_49]: (k9_subset_1(A_8, B_49, B_49)=B_49)), inference(resolution, [status(thm)], [c_53, c_79])).
% 2.29/1.28  tff(c_214, plain, (![A_81, B_82, D_83]: (k9_subset_1(u1_struct_0(A_81), B_82, D_83)!='#skF_2'(A_81, B_82) | ~v3_pre_topc(D_83, A_81) | ~m1_subset_1(D_83, k1_zfmisc_1(u1_struct_0(A_81))) | v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.29/1.28  tff(c_238, plain, (![A_87, B_88]: ('#skF_2'(A_87, B_88)!=B_88 | ~v3_pre_topc(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(superposition, [status(thm), theory('equality')], [c_82, c_214])).
% 2.29/1.28  tff(c_245, plain, (![A_87]: ('#skF_2'(A_87, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_87) | v2_tex_2('#skF_4', A_87) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_53, c_238])).
% 2.29/1.28  tff(c_251, plain, (![A_89]: ('#skF_2'(A_89, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_89) | v2_tex_2('#skF_4', A_89) | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_245])).
% 2.29/1.28  tff(c_254, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_177, c_251])).
% 2.29/1.28  tff(c_260, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_124, c_254])).
% 2.29/1.28  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_260])).
% 2.29/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.28  
% 2.29/1.28  Inference rules
% 2.29/1.28  ----------------------
% 2.29/1.28  #Ref     : 0
% 2.29/1.28  #Sup     : 46
% 2.29/1.28  #Fact    : 0
% 2.29/1.28  #Define  : 0
% 2.29/1.28  #Split   : 0
% 2.29/1.28  #Chain   : 0
% 2.29/1.28  #Close   : 0
% 2.29/1.28  
% 2.29/1.28  Ordering : KBO
% 2.29/1.28  
% 2.29/1.28  Simplification rules
% 2.29/1.28  ----------------------
% 2.29/1.28  #Subsume      : 2
% 2.29/1.28  #Demod        : 37
% 2.29/1.28  #Tautology    : 17
% 2.29/1.28  #SimpNegUnit  : 7
% 2.29/1.28  #BackRed      : 3
% 2.29/1.28  
% 2.29/1.28  #Partial instantiations: 0
% 2.29/1.28  #Strategies tried      : 1
% 2.29/1.28  
% 2.29/1.28  Timing (in seconds)
% 2.29/1.28  ----------------------
% 2.29/1.28  Preprocessing        : 0.29
% 2.29/1.28  Parsing              : 0.16
% 2.29/1.28  CNF conversion       : 0.02
% 2.29/1.28  Main loop            : 0.22
% 2.29/1.28  Inferencing          : 0.09
% 2.29/1.28  Reduction            : 0.06
% 2.29/1.28  Demodulation         : 0.05
% 2.29/1.28  BG Simplification    : 0.01
% 2.29/1.28  Subsumption          : 0.04
% 2.29/1.28  Abstraction          : 0.01
% 2.29/1.28  MUC search           : 0.00
% 2.29/1.28  Cooper               : 0.00
% 2.29/1.28  Total                : 0.55
% 2.29/1.28  Index Insertion      : 0.00
% 2.29/1.28  Index Deletion       : 0.00
% 2.29/1.28  Index Matching       : 0.00
% 2.29/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
