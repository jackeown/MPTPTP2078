%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 162 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 357 expanded)
%              Number of equality atoms :    4 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    v1_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_61,plain,(
    ! [B_65,A_66] :
      ( l1_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_61])).

tff(c_75,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70])).

tff(c_36,plain,(
    ! [A_49] :
      ( m1_pre_topc(A_49,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_96,plain,(
    ! [B_74,A_75] :
      ( m1_subset_1(u1_struct_0(B_74),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_109,plain,(
    ! [B_74] :
      ( m1_subset_1(u1_struct_0(B_74),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_74,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_96])).

tff(c_114,plain,(
    ! [B_76] :
      ( m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_76,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_109])).

tff(c_40,plain,(
    ! [B_51] :
      ( ~ v1_subset_1(B_51,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_40])).

tff(c_128,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_121])).

tff(c_124,plain,
    ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_114])).

tff(c_129,plain,(
    ~ m1_pre_topc('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_149,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_149])).

tff(c_154,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_276,plain,(
    ! [B_86,A_87] :
      ( v1_subset_1(u1_struct_0(B_86),u1_struct_0(A_87))
      | ~ v1_tex_2(B_86,A_87)
      | ~ m1_subset_1(u1_struct_0(B_86),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_282,plain,
    ( v1_subset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ v1_tex_2('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_154,c_276])).

tff(c_298,plain,
    ( v1_subset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ v1_tex_2('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_282])).

tff(c_299,plain,
    ( ~ v1_tex_2('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_298])).

tff(c_307,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_310,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_307])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_310])).

tff(c_316,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_42,plain,(
    ! [B_54,A_52] :
      ( m1_subset_1(u1_struct_0(B_54),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_339,plain,(
    ! [B_90,A_91] :
      ( v1_subset_1(u1_struct_0(B_90),u1_struct_0(A_91))
      | ~ v1_tex_2(B_90,A_91)
      | ~ m1_pre_topc(B_90,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_42,c_276])).

tff(c_352,plain,(
    ! [B_90] :
      ( v1_subset_1(u1_struct_0(B_90),u1_struct_0('#skF_6'))
      | ~ v1_tex_2(B_90,'#skF_5')
      | ~ m1_pre_topc(B_90,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_339])).

tff(c_360,plain,(
    ! [B_93] :
      ( v1_subset_1(u1_struct_0(B_93),u1_struct_0('#skF_6'))
      | ~ v1_tex_2(B_93,'#skF_5')
      | ~ m1_pre_topc(B_93,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_352])).

tff(c_111,plain,(
    ! [A_75] :
      ( ~ v1_subset_1(u1_struct_0(A_75),u1_struct_0(A_75))
      | ~ m1_pre_topc(A_75,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_96,c_40])).

tff(c_364,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v1_tex_2('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_360,c_111])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_75,c_316,c_364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  
% 2.18/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.18/1.33  
% 2.18/1.33  %Foreground sorts:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Background operators:
% 2.18/1.33  
% 2.18/1.33  
% 2.18/1.33  %Foreground operators:
% 2.18/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.18/1.33  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.18/1.33  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.18/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.18/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.18/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.18/1.33  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.18/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.33  
% 2.53/1.35  tff(f_110, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.53/1.35  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.53/1.35  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.53/1.35  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l17_tex_2)).
% 2.53/1.35  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.53/1.35  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.53/1.35  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.53/1.35  tff(c_48, plain, (v1_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.53/1.35  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.53/1.35  tff(c_61, plain, (![B_65, A_66]: (l1_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.35  tff(c_70, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_52, c_61])).
% 2.53/1.35  tff(c_75, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_70])).
% 2.53/1.35  tff(c_36, plain, (![A_49]: (m1_pre_topc(A_49, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.35  tff(c_50, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.53/1.35  tff(c_96, plain, (![B_74, A_75]: (m1_subset_1(u1_struct_0(B_74), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.35  tff(c_109, plain, (![B_74]: (m1_subset_1(u1_struct_0(B_74), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_74, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_96])).
% 2.53/1.35  tff(c_114, plain, (![B_76]: (m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_76, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_109])).
% 2.53/1.35  tff(c_40, plain, (![B_51]: (~v1_subset_1(B_51, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_121, plain, (~v1_subset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_114, c_40])).
% 2.53/1.35  tff(c_128, plain, (~v1_subset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_121])).
% 2.53/1.35  tff(c_124, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_50, c_114])).
% 2.53/1.35  tff(c_129, plain, (~m1_pre_topc('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_124])).
% 2.53/1.35  tff(c_149, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_129])).
% 2.53/1.35  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_149])).
% 2.53/1.35  tff(c_154, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_124])).
% 2.53/1.35  tff(c_276, plain, (![B_86, A_87]: (v1_subset_1(u1_struct_0(B_86), u1_struct_0(A_87)) | ~v1_tex_2(B_86, A_87) | ~m1_subset_1(u1_struct_0(B_86), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.35  tff(c_282, plain, (v1_subset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')) | ~v1_tex_2('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_154, c_276])).
% 2.53/1.35  tff(c_298, plain, (v1_subset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')) | ~v1_tex_2('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_282])).
% 2.53/1.35  tff(c_299, plain, (~v1_tex_2('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_128, c_298])).
% 2.53/1.35  tff(c_307, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_299])).
% 2.53/1.35  tff(c_310, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_307])).
% 2.53/1.35  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_310])).
% 2.53/1.35  tff(c_316, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_299])).
% 2.53/1.35  tff(c_42, plain, (![B_54, A_52]: (m1_subset_1(u1_struct_0(B_54), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.35  tff(c_339, plain, (![B_90, A_91]: (v1_subset_1(u1_struct_0(B_90), u1_struct_0(A_91)) | ~v1_tex_2(B_90, A_91) | ~m1_pre_topc(B_90, A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_42, c_276])).
% 2.53/1.35  tff(c_352, plain, (![B_90]: (v1_subset_1(u1_struct_0(B_90), u1_struct_0('#skF_6')) | ~v1_tex_2(B_90, '#skF_5') | ~m1_pre_topc(B_90, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_339])).
% 2.53/1.35  tff(c_360, plain, (![B_93]: (v1_subset_1(u1_struct_0(B_93), u1_struct_0('#skF_6')) | ~v1_tex_2(B_93, '#skF_5') | ~m1_pre_topc(B_93, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_352])).
% 2.53/1.35  tff(c_111, plain, (![A_75]: (~v1_subset_1(u1_struct_0(A_75), u1_struct_0(A_75)) | ~m1_pre_topc(A_75, A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_96, c_40])).
% 2.53/1.35  tff(c_364, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v1_tex_2('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_360, c_111])).
% 2.53/1.35  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_75, c_316, c_364])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 0
% 2.53/1.35  #Sup     : 56
% 2.53/1.35  #Fact    : 0
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 3
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 10
% 2.53/1.35  #Demod        : 51
% 2.53/1.35  #Tautology    : 18
% 2.53/1.35  #SimpNegUnit  : 5
% 2.53/1.35  #BackRed      : 0
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.35  Preprocessing        : 0.33
% 2.53/1.35  Parsing              : 0.16
% 2.53/1.35  CNF conversion       : 0.03
% 2.53/1.35  Main loop            : 0.21
% 2.53/1.35  Inferencing          : 0.07
% 2.53/1.35  Reduction            : 0.06
% 2.53/1.35  Demodulation         : 0.04
% 2.53/1.35  BG Simplification    : 0.02
% 2.53/1.35  Subsumption          : 0.05
% 2.53/1.35  Abstraction          : 0.01
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.56
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
