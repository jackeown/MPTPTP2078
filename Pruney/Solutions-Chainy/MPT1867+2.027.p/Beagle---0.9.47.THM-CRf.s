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
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 190 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  115 ( 440 expanded)
%              Number of equality atoms :   22 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_53,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [A_4] : k4_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_14])).

tff(c_116,plain,(
    ! [A_63,B_64] :
      ( r1_tarski('#skF_2'(A_63,B_64),B_64)
      | v2_tex_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_65] :
      ( r1_tarski('#skF_2'(A_65,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_55,c_116])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k1_xboole_0
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = '#skF_4'
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_124,plain,(
    ! [A_65] :
      ( k4_xboole_0('#skF_2'(A_65,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_121,c_82])).

tff(c_127,plain,(
    ! [A_66] :
      ( '#skF_2'(A_66,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_124])).

tff(c_130,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_133,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_130])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_144,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_2'(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [B_14,A_12] :
      ( v3_pre_topc(B_14,A_12)
      | ~ v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_172,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc('#skF_2'(A_72,B_73),A_72)
      | ~ v1_xboole_0('#skF_2'(A_72,B_73))
      | ~ v2_pre_topc(A_72)
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_188,plain,(
    ! [A_77] :
      ( v3_pre_topc('#skF_2'(A_77,'#skF_4'),A_77)
      | ~ v1_xboole_0('#skF_2'(A_77,'#skF_4'))
      | ~ v2_pre_topc(A_77)
      | v2_tex_2('#skF_4',A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_55,c_172])).

tff(c_191,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_188])).

tff(c_193,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_36,c_133,c_191])).

tff(c_194,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_193])).

tff(c_88,plain,(
    ! [A_50,B_51,C_52] :
      ( k9_subset_1(A_50,B_51,B_51) = B_51
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_8,B_51] : k9_subset_1(A_8,B_51,B_51) = B_51 ),
    inference(resolution,[status(thm)],[c_55,c_88])).

tff(c_223,plain,(
    ! [A_83,B_84,D_85] :
      ( k9_subset_1(u1_struct_0(A_83),B_84,D_85) != '#skF_2'(A_83,B_84)
      | ~ v3_pre_topc(D_85,A_83)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0(A_83)))
      | v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_227,plain,(
    ! [A_86,B_87] :
      ( '#skF_2'(A_86,B_87) != B_87
      | ~ v3_pre_topc(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_223])).

tff(c_232,plain,(
    ! [A_86] :
      ( '#skF_2'(A_86,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_86)
      | v2_tex_2('#skF_4',A_86)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_55,c_227])).

tff(c_237,plain,(
    ! [A_88] :
      ( '#skF_2'(A_88,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_88)
      | v2_tex_2('#skF_4',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_232])).

tff(c_240,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_237])).

tff(c_246,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_133,c_240])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.24  
% 2.40/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.24  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.40/1.24  
% 2.40/1.24  %Foreground sorts:
% 2.40/1.24  
% 2.40/1.24  
% 2.40/1.24  %Background operators:
% 2.40/1.24  
% 2.40/1.24  
% 2.40/1.24  %Foreground operators:
% 2.40/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.40/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.40/1.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.40/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.40/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.40/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.40/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.40/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.24  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.40/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.24  
% 2.40/1.26  tff(f_95, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.40/1.26  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.26  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.40/1.26  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.40/1.26  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.40/1.26  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.40/1.26  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.40/1.26  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.40/1.26  tff(c_32, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.26  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.26  tff(c_36, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.26  tff(c_44, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.40/1.26  tff(c_53, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.40/1.26  tff(c_10, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.40/1.26  tff(c_62, plain, (![A_4]: (k4_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_10])).
% 2.40/1.26  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.40/1.26  tff(c_55, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_14])).
% 2.40/1.26  tff(c_116, plain, (![A_63, B_64]: (r1_tarski('#skF_2'(A_63, B_64), B_64) | v2_tex_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.26  tff(c_121, plain, (![A_65]: (r1_tarski('#skF_2'(A_65, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_55, c_116])).
% 2.40/1.26  tff(c_8, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k1_xboole_0 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.40/1.26  tff(c_82, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)='#skF_4' | ~r1_tarski(A_2, B_3))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_8])).
% 2.40/1.26  tff(c_124, plain, (![A_65]: (k4_xboole_0('#skF_2'(A_65, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_121, c_82])).
% 2.40/1.26  tff(c_127, plain, (![A_66]: ('#skF_2'(A_66, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_66) | ~l1_pre_topc(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_124])).
% 2.40/1.26  tff(c_130, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_127, c_32])).
% 2.40/1.26  tff(c_133, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_130])).
% 2.40/1.26  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.26  tff(c_144, plain, (![A_67, B_68]: (m1_subset_1('#skF_2'(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.26  tff(c_18, plain, (![B_14, A_12]: (v3_pre_topc(B_14, A_12) | ~v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.26  tff(c_172, plain, (![A_72, B_73]: (v3_pre_topc('#skF_2'(A_72, B_73), A_72) | ~v1_xboole_0('#skF_2'(A_72, B_73)) | ~v2_pre_topc(A_72) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.40/1.26  tff(c_188, plain, (![A_77]: (v3_pre_topc('#skF_2'(A_77, '#skF_4'), A_77) | ~v1_xboole_0('#skF_2'(A_77, '#skF_4')) | ~v2_pre_topc(A_77) | v2_tex_2('#skF_4', A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_55, c_172])).
% 2.40/1.26  tff(c_191, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_188])).
% 2.40/1.26  tff(c_193, plain, (v3_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_36, c_133, c_191])).
% 2.40/1.26  tff(c_194, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_193])).
% 2.40/1.26  tff(c_88, plain, (![A_50, B_51, C_52]: (k9_subset_1(A_50, B_51, B_51)=B_51 | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.26  tff(c_91, plain, (![A_8, B_51]: (k9_subset_1(A_8, B_51, B_51)=B_51)), inference(resolution, [status(thm)], [c_55, c_88])).
% 2.40/1.26  tff(c_223, plain, (![A_83, B_84, D_85]: (k9_subset_1(u1_struct_0(A_83), B_84, D_85)!='#skF_2'(A_83, B_84) | ~v3_pre_topc(D_85, A_83) | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0(A_83))) | v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.40/1.26  tff(c_227, plain, (![A_86, B_87]: ('#skF_2'(A_86, B_87)!=B_87 | ~v3_pre_topc(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_91, c_223])).
% 2.40/1.26  tff(c_232, plain, (![A_86]: ('#skF_2'(A_86, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_86) | v2_tex_2('#skF_4', A_86) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_55, c_227])).
% 2.40/1.26  tff(c_237, plain, (![A_88]: ('#skF_2'(A_88, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_88) | v2_tex_2('#skF_4', A_88) | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_232])).
% 2.40/1.26  tff(c_240, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_194, c_237])).
% 2.40/1.26  tff(c_246, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_133, c_240])).
% 2.40/1.26  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_246])).
% 2.40/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.26  
% 2.40/1.26  Inference rules
% 2.40/1.26  ----------------------
% 2.40/1.26  #Ref     : 0
% 2.40/1.26  #Sup     : 40
% 2.40/1.26  #Fact    : 0
% 2.40/1.26  #Define  : 0
% 2.40/1.26  #Split   : 0
% 2.40/1.26  #Chain   : 0
% 2.40/1.26  #Close   : 0
% 2.40/1.26  
% 2.40/1.26  Ordering : KBO
% 2.40/1.26  
% 2.40/1.26  Simplification rules
% 2.40/1.26  ----------------------
% 2.40/1.26  #Subsume      : 1
% 2.40/1.26  #Demod        : 39
% 2.40/1.26  #Tautology    : 18
% 2.40/1.26  #SimpNegUnit  : 7
% 2.40/1.26  #BackRed      : 3
% 2.40/1.26  
% 2.40/1.26  #Partial instantiations: 0
% 2.40/1.26  #Strategies tried      : 1
% 2.40/1.26  
% 2.40/1.26  Timing (in seconds)
% 2.40/1.26  ----------------------
% 2.40/1.26  Preprocessing        : 0.29
% 2.40/1.26  Parsing              : 0.16
% 2.40/1.26  CNF conversion       : 0.02
% 2.40/1.26  Main loop            : 0.20
% 2.40/1.26  Inferencing          : 0.08
% 2.40/1.26  Reduction            : 0.06
% 2.40/1.26  Demodulation         : 0.04
% 2.40/1.26  BG Simplification    : 0.01
% 2.40/1.26  Subsumption          : 0.04
% 2.40/1.26  Abstraction          : 0.01
% 2.40/1.26  MUC search           : 0.00
% 2.40/1.26  Cooper               : 0.00
% 2.40/1.26  Total                : 0.53
% 2.40/1.26  Index Insertion      : 0.00
% 2.40/1.26  Index Deletion       : 0.00
% 2.40/1.26  Index Matching       : 0.00
% 2.40/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
