%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 208 expanded)
%              Number of leaves         :   30 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 484 expanded)
%              Number of equality atoms :   18 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_93,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_18])).

tff(c_103,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    ! [A_12,A_68] :
      ( ~ v1_xboole_0(A_12)
      | ~ r2_hidden(A_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_61,c_103])).

tff(c_112,plain,(
    ! [A_72] : ~ r2_hidden(A_72,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_117,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_176,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_3'(A_87,B_88),B_88)
      | v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_181,plain,(
    ! [A_89] :
      ( r1_tarski('#skF_3'(A_89,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_61,c_176])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_89] :
      ( '#skF_3'(A_89,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5','#skF_3'(A_89,'#skF_5'))
      | v2_tex_2('#skF_5',A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_181,c_10])).

tff(c_199,plain,(
    ! [A_90] :
      ( '#skF_3'(A_90,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_190])).

tff(c_202,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_38])).

tff(c_205,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_202])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_238,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1('#skF_3'(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( v3_pre_topc(B_21,A_19)
      | ~ v1_xboole_0(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_583,plain,(
    ! [A_133,B_134] :
      ( v3_pre_topc('#skF_3'(A_133,B_134),A_133)
      | ~ v1_xboole_0('#skF_3'(A_133,B_134))
      | ~ v2_pre_topc(A_133)
      | v2_tex_2(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_238,c_24])).

tff(c_610,plain,(
    ! [A_137] :
      ( v3_pre_topc('#skF_3'(A_137,'#skF_5'),A_137)
      | ~ v1_xboole_0('#skF_3'(A_137,'#skF_5'))
      | ~ v2_pre_topc(A_137)
      | v2_tex_2('#skF_5',A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_61,c_583])).

tff(c_619,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_610])).

tff(c_621,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_205,c_619])).

tff(c_622,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_621])).

tff(c_85,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(A_58,B_59,B_59) = B_59
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [A_12,B_59] : k9_subset_1(A_12,B_59,B_59) = B_59 ),
    inference(resolution,[status(thm)],[c_61,c_85])).

tff(c_456,plain,(
    ! [A_113,B_114,D_115] :
      ( k9_subset_1(u1_struct_0(A_113),B_114,D_115) != '#skF_3'(A_113,B_114)
      | ~ v3_pre_topc(D_115,A_113)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_637,plain,(
    ! [A_142,B_143] :
      ( '#skF_3'(A_142,B_143) != B_143
      | ~ v3_pre_topc(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | v2_tex_2(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_456])).

tff(c_646,plain,(
    ! [A_142] :
      ( '#skF_3'(A_142,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_142)
      | v2_tex_2('#skF_5',A_142)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_61,c_637])).

tff(c_653,plain,(
    ! [A_144] :
      ( '#skF_3'(A_144,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_144)
      | v2_tex_2('#skF_5',A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_646])).

tff(c_656,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_622,c_653])).

tff(c_662,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_205,c_656])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_662])).

tff(c_665,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_665,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.43  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_4 > #skF_1
% 3.07/1.43  
% 3.07/1.43  %Foreground sorts:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Background operators:
% 3.07/1.43  
% 3.07/1.43  
% 3.07/1.43  %Foreground operators:
% 3.07/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.07/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.07/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.07/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.07/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.07/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.07/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.07/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.07/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.43  
% 3.07/1.45  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.07/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.07/1.45  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.07/1.45  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.07/1.45  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.07/1.45  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.07/1.45  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.45  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.07/1.45  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 3.07/1.45  tff(c_38, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.07/1.45  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.07/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.45  tff(c_42, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.07/1.45  tff(c_51, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.45  tff(c_55, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_51])).
% 3.07/1.45  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.07/1.45  tff(c_61, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_18])).
% 3.07/1.45  tff(c_103, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.07/1.45  tff(c_106, plain, (![A_12, A_68]: (~v1_xboole_0(A_12) | ~r2_hidden(A_68, '#skF_5'))), inference(resolution, [status(thm)], [c_61, c_103])).
% 3.07/1.45  tff(c_112, plain, (![A_72]: (~r2_hidden(A_72, '#skF_5'))), inference(splitLeft, [status(thm)], [c_106])).
% 3.07/1.45  tff(c_117, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_112])).
% 3.07/1.45  tff(c_176, plain, (![A_87, B_88]: (r1_tarski('#skF_3'(A_87, B_88), B_88) | v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.45  tff(c_181, plain, (![A_89]: (r1_tarski('#skF_3'(A_89, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_61, c_176])).
% 3.07/1.45  tff(c_10, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.45  tff(c_190, plain, (![A_89]: ('#skF_3'(A_89, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', '#skF_3'(A_89, '#skF_5')) | v2_tex_2('#skF_5', A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_181, c_10])).
% 3.07/1.45  tff(c_199, plain, (![A_90]: ('#skF_3'(A_90, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_190])).
% 3.07/1.45  tff(c_202, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_199, c_38])).
% 3.07/1.45  tff(c_205, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_202])).
% 3.07/1.45  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.07/1.45  tff(c_238, plain, (![A_93, B_94]: (m1_subset_1('#skF_3'(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.45  tff(c_24, plain, (![B_21, A_19]: (v3_pre_topc(B_21, A_19) | ~v1_xboole_0(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.07/1.45  tff(c_583, plain, (![A_133, B_134]: (v3_pre_topc('#skF_3'(A_133, B_134), A_133) | ~v1_xboole_0('#skF_3'(A_133, B_134)) | ~v2_pre_topc(A_133) | v2_tex_2(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_238, c_24])).
% 3.07/1.45  tff(c_610, plain, (![A_137]: (v3_pre_topc('#skF_3'(A_137, '#skF_5'), A_137) | ~v1_xboole_0('#skF_3'(A_137, '#skF_5')) | ~v2_pre_topc(A_137) | v2_tex_2('#skF_5', A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_61, c_583])).
% 3.07/1.45  tff(c_619, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_205, c_610])).
% 3.07/1.45  tff(c_621, plain, (v3_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_205, c_619])).
% 3.07/1.45  tff(c_622, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_621])).
% 3.07/1.45  tff(c_85, plain, (![A_58, B_59, C_60]: (k9_subset_1(A_58, B_59, B_59)=B_59 | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.45  tff(c_88, plain, (![A_12, B_59]: (k9_subset_1(A_12, B_59, B_59)=B_59)), inference(resolution, [status(thm)], [c_61, c_85])).
% 3.07/1.45  tff(c_456, plain, (![A_113, B_114, D_115]: (k9_subset_1(u1_struct_0(A_113), B_114, D_115)!='#skF_3'(A_113, B_114) | ~v3_pre_topc(D_115, A_113) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_113))) | v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.45  tff(c_637, plain, (![A_142, B_143]: ('#skF_3'(A_142, B_143)!=B_143 | ~v3_pre_topc(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | v2_tex_2(B_143, A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(superposition, [status(thm), theory('equality')], [c_88, c_456])).
% 3.07/1.45  tff(c_646, plain, (![A_142]: ('#skF_3'(A_142, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_142) | v2_tex_2('#skF_5', A_142) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_61, c_637])).
% 3.07/1.45  tff(c_653, plain, (![A_144]: ('#skF_3'(A_144, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_144) | v2_tex_2('#skF_5', A_144) | ~l1_pre_topc(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_646])).
% 3.07/1.45  tff(c_656, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_622, c_653])).
% 3.07/1.45  tff(c_662, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_205, c_656])).
% 3.07/1.45  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_662])).
% 3.07/1.45  tff(c_665, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitRight, [status(thm)], [c_106])).
% 3.07/1.45  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_665, c_42])).
% 3.07/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.45  
% 3.07/1.45  Inference rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Ref     : 0
% 3.07/1.45  #Sup     : 140
% 3.07/1.45  #Fact    : 2
% 3.07/1.45  #Define  : 0
% 3.07/1.45  #Split   : 2
% 3.07/1.45  #Chain   : 0
% 3.07/1.45  #Close   : 0
% 3.07/1.45  
% 3.07/1.45  Ordering : KBO
% 3.07/1.45  
% 3.07/1.45  Simplification rules
% 3.07/1.45  ----------------------
% 3.07/1.45  #Subsume      : 48
% 3.07/1.45  #Demod        : 53
% 3.07/1.45  #Tautology    : 28
% 3.07/1.45  #SimpNegUnit  : 14
% 3.07/1.45  #BackRed      : 2
% 3.07/1.45  
% 3.07/1.45  #Partial instantiations: 0
% 3.07/1.45  #Strategies tried      : 1
% 3.07/1.45  
% 3.07/1.45  Timing (in seconds)
% 3.07/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.32
% 3.07/1.45  Parsing              : 0.18
% 3.07/1.45  CNF conversion       : 0.03
% 3.07/1.45  Main loop            : 0.36
% 3.07/1.45  Inferencing          : 0.13
% 3.07/1.45  Reduction            : 0.10
% 3.07/1.45  Demodulation         : 0.07
% 3.07/1.45  BG Simplification    : 0.02
% 3.07/1.45  Subsumption          : 0.07
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.46  MUC search           : 0.00
% 3.07/1.46  Cooper               : 0.00
% 3.07/1.46  Total                : 0.72
% 3.07/1.46  Index Insertion      : 0.00
% 3.07/1.46  Index Deletion       : 0.00
% 3.07/1.46  Index Matching       : 0.00
% 3.07/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
