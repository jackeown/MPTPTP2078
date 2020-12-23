%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:28 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 171 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 401 expanded)
%              Number of equality atoms :   18 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_48,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_16])).

tff(c_127,plain,(
    ! [A_63,B_64] :
      ( r1_tarski('#skF_2'(A_63,B_64),B_64)
      | v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_132,plain,(
    ! [A_65] :
      ( r1_tarski('#skF_2'(A_65,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_67,c_127])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_12])).

tff(c_76,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_76])).

tff(c_142,plain,(
    ! [A_66] :
      ( '#skF_2'(A_66,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_132,c_81])).

tff(c_145,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_34])).

tff(c_148,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_149,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_2'(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v4_pre_topc(B_14,A_12)
      | ~ v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_201,plain,(
    ! [A_78,B_79] :
      ( v4_pre_topc('#skF_2'(A_78,B_79),A_78)
      | ~ v1_xboole_0('#skF_2'(A_78,B_79))
      | ~ v2_pre_topc(A_78)
      | v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_149,c_20])).

tff(c_209,plain,(
    ! [A_80] :
      ( v4_pre_topc('#skF_2'(A_80,'#skF_4'),A_80)
      | ~ v1_xboole_0('#skF_2'(A_80,'#skF_4'))
      | ~ v2_pre_topc(A_80)
      | v2_tex_2('#skF_4',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_67,c_201])).

tff(c_212,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_209])).

tff(c_214,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_148,c_212])).

tff(c_215,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_214])).

tff(c_86,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,B_50) = B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_8,B_50] : k9_subset_1(A_8,B_50,B_50) = B_50 ),
    inference(resolution,[status(thm)],[c_67,c_86])).

tff(c_259,plain,(
    ! [A_88,B_89,D_90] :
      ( k9_subset_1(u1_struct_0(A_88),B_89,D_90) != '#skF_2'(A_88,B_89)
      | ~ v4_pre_topc(D_90,A_88)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_300,plain,(
    ! [A_97,B_98] :
      ( '#skF_2'(A_97,B_98) != B_98
      | ~ v4_pre_topc(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_259])).

tff(c_307,plain,(
    ! [A_97] :
      ( '#skF_2'(A_97,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_97)
      | v2_tex_2('#skF_4',A_97)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_67,c_300])).

tff(c_313,plain,(
    ! [A_99] :
      ( '#skF_2'(A_99,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_99)
      | v2_tex_2('#skF_4',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_307])).

tff(c_316,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_313])).

tff(c_322,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_148,c_316])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.23/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.27  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.23/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.27  
% 2.23/1.28  tff(f_97, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.23/1.28  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.28  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.23/1.28  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.23/1.28  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.28  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.28  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.23/1.28  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.23/1.28  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.28  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.28  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.28  tff(c_48, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.23/1.28  tff(c_57, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_48])).
% 2.23/1.28  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.28  tff(c_67, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_16])).
% 2.23/1.28  tff(c_127, plain, (![A_63, B_64]: (r1_tarski('#skF_2'(A_63, B_64), B_64) | v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.28  tff(c_132, plain, (![A_65]: (r1_tarski('#skF_2'(A_65, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_67, c_127])).
% 2.23/1.28  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.28  tff(c_59, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_12])).
% 2.23/1.28  tff(c_76, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.28  tff(c_81, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_59, c_76])).
% 2.23/1.28  tff(c_142, plain, (![A_66]: ('#skF_2'(A_66, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_132, c_81])).
% 2.23/1.28  tff(c_145, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_142, c_34])).
% 2.23/1.28  tff(c_148, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_145])).
% 2.23/1.28  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.23/1.28  tff(c_149, plain, (![A_67, B_68]: (m1_subset_1('#skF_2'(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.28  tff(c_20, plain, (![B_14, A_12]: (v4_pre_topc(B_14, A_12) | ~v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.28  tff(c_201, plain, (![A_78, B_79]: (v4_pre_topc('#skF_2'(A_78, B_79), A_78) | ~v1_xboole_0('#skF_2'(A_78, B_79)) | ~v2_pre_topc(A_78) | v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_149, c_20])).
% 2.23/1.28  tff(c_209, plain, (![A_80]: (v4_pre_topc('#skF_2'(A_80, '#skF_4'), A_80) | ~v1_xboole_0('#skF_2'(A_80, '#skF_4')) | ~v2_pre_topc(A_80) | v2_tex_2('#skF_4', A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_67, c_201])).
% 2.23/1.28  tff(c_212, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_209])).
% 2.23/1.28  tff(c_214, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_148, c_212])).
% 2.23/1.28  tff(c_215, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_214])).
% 2.23/1.28  tff(c_86, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, B_50)=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.28  tff(c_89, plain, (![A_8, B_50]: (k9_subset_1(A_8, B_50, B_50)=B_50)), inference(resolution, [status(thm)], [c_67, c_86])).
% 2.23/1.28  tff(c_259, plain, (![A_88, B_89, D_90]: (k9_subset_1(u1_struct_0(A_88), B_89, D_90)!='#skF_2'(A_88, B_89) | ~v4_pre_topc(D_90, A_88) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(A_88))) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.28  tff(c_300, plain, (![A_97, B_98]: ('#skF_2'(A_97, B_98)!=B_98 | ~v4_pre_topc(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(superposition, [status(thm), theory('equality')], [c_89, c_259])).
% 2.23/1.28  tff(c_307, plain, (![A_97]: ('#skF_2'(A_97, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_97) | v2_tex_2('#skF_4', A_97) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_67, c_300])).
% 2.23/1.28  tff(c_313, plain, (![A_99]: ('#skF_2'(A_99, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_99) | v2_tex_2('#skF_4', A_99) | ~l1_pre_topc(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_307])).
% 2.23/1.28  tff(c_316, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_215, c_313])).
% 2.23/1.28  tff(c_322, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_148, c_316])).
% 2.23/1.28  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_322])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 58
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 0
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 4
% 2.23/1.28  #Demod        : 42
% 2.23/1.28  #Tautology    : 22
% 2.23/1.28  #SimpNegUnit  : 8
% 2.23/1.28  #BackRed      : 3
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.29  Preprocessing        : 0.29
% 2.23/1.29  Parsing              : 0.16
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.23
% 2.23/1.29  Inferencing          : 0.09
% 2.23/1.29  Reduction            : 0.07
% 2.23/1.29  Demodulation         : 0.05
% 2.23/1.29  BG Simplification    : 0.02
% 2.23/1.29  Subsumption          : 0.05
% 2.23/1.29  Abstraction          : 0.01
% 2.23/1.29  MUC search           : 0.00
% 2.23/1.29  Cooper               : 0.00
% 2.23/1.29  Total                : 0.56
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
