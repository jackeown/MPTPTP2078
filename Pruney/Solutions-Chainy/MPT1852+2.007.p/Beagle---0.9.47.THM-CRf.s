%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 271 expanded)
%              Number of leaves         :   19 (  97 expanded)
%              Depth                    :   17
%              Number of atoms          :   92 ( 690 expanded)
%              Number of equality atoms :   21 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_16,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),u1_pre_topc(A_8))
      | v3_tdlat_3(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_1'(A_8),k1_zfmisc_1(u1_struct_0(A_8)))
      | v3_tdlat_3(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_37,plain,(
    ! [D_17,B_18,C_19,A_20] :
      ( D_17 = B_18
      | g1_pre_topc(C_19,D_17) != g1_pre_topc(A_20,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [B_25,A_26] :
      ( u1_pre_topc('#skF_2') = B_25
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_26,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_55,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_63,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_55])).

tff(c_65,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_83,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_92,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_76,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_20])).

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_pre_topc(C_6,D_7) != g1_pre_topc(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_2') = C_6
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_6,D_7)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_124,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_2') = C_6
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_116])).

tff(c_130,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_124])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_30),B_31),u1_pre_topc(A_30))
      | ~ r2_hidden(B_31,u1_pre_topc(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v3_tdlat_3(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_2'),B_31),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_31,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_96])).

tff(c_106,plain,(
    ! [B_31] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_2'),B_31),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_31,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_65,c_103])).

tff(c_181,plain,(
    ! [B_38] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_38),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_38,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_106])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_8),'#skF_1'(A_8)),u1_pre_topc(A_8))
      | v3_tdlat_3(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_185,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_181,c_10])).

tff(c_188,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_189,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_188])).

tff(c_190,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_193,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_190])).

tff(c_196,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_196])).

tff(c_199,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_203,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_206,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_203])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  %$ r2_hidden > m1_subset_1 > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.21  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.93/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.21  
% 2.03/1.22  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 2.03/1.22  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 2.03/1.22  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.03/1.22  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.03/1.22  tff(c_16, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_22, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_12, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), u1_pre_topc(A_8)) | v3_tdlat_3(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.22  tff(c_14, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), k1_zfmisc_1(u1_struct_0(A_8))) | v3_tdlat_3(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.22  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.22  tff(c_20, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_37, plain, (![D_17, B_18, C_19, A_20]: (D_17=B_18 | g1_pre_topc(C_19, D_17)!=g1_pre_topc(A_20, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.22  tff(c_51, plain, (![B_25, A_26]: (u1_pre_topc('#skF_2')=B_25 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_26, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_37])).
% 2.03/1.22  tff(c_55, plain, (![A_1]: (u1_pre_topc(A_1)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_51])).
% 2.03/1.22  tff(c_63, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_55])).
% 2.03/1.22  tff(c_65, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 2.03/1.22  tff(c_83, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.03/1.22  tff(c_92, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_83])).
% 2.03/1.22  tff(c_76, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_20])).
% 2.03/1.22  tff(c_6, plain, (![C_6, A_2, D_7, B_3]: (C_6=A_2 | g1_pre_topc(C_6, D_7)!=g1_pre_topc(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.22  tff(c_116, plain, (![C_6, D_7]: (u1_struct_0('#skF_2')=C_6 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_6, D_7) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 2.03/1.22  tff(c_124, plain, (![C_6, D_7]: (u1_struct_0('#skF_2')=C_6 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_116])).
% 2.03/1.22  tff(c_130, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_124])).
% 2.03/1.22  tff(c_18, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_96, plain, (![A_30, B_31]: (r2_hidden(k6_subset_1(u1_struct_0(A_30), B_31), u1_pre_topc(A_30)) | ~r2_hidden(B_31, u1_pre_topc(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~v3_tdlat_3(A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.22  tff(c_103, plain, (![B_31]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_2'), B_31), u1_pre_topc('#skF_3')) | ~r2_hidden(B_31, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_96])).
% 2.03/1.22  tff(c_106, plain, (![B_31]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_2'), B_31), u1_pre_topc('#skF_3')) | ~r2_hidden(B_31, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_65, c_103])).
% 2.03/1.22  tff(c_181, plain, (![B_38]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_38), u1_pre_topc('#skF_3')) | ~r2_hidden(B_38, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_106])).
% 2.03/1.22  tff(c_10, plain, (![A_8]: (~r2_hidden(k6_subset_1(u1_struct_0(A_8), '#skF_1'(A_8)), u1_pre_topc(A_8)) | v3_tdlat_3(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.22  tff(c_185, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_181, c_10])).
% 2.03/1.22  tff(c_188, plain, (v3_tdlat_3('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_185])).
% 2.03/1.22  tff(c_189, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_16, c_188])).
% 2.03/1.22  tff(c_190, plain, (~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_189])).
% 2.03/1.22  tff(c_193, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_190])).
% 2.03/1.22  tff(c_196, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_193])).
% 2.03/1.22  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_196])).
% 2.03/1.22  tff(c_199, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_189])).
% 2.03/1.22  tff(c_203, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_199])).
% 2.03/1.22  tff(c_206, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_203])).
% 2.03/1.22  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_206])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 6
% 2.03/1.22  #Sup     : 33
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 1
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.22  ----------------------
% 2.03/1.23  #Subsume      : 8
% 2.03/1.23  #Demod        : 43
% 2.03/1.23  #Tautology    : 22
% 2.03/1.23  #SimpNegUnit  : 3
% 2.03/1.23  #BackRed      : 5
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.28
% 2.08/1.23  Parsing              : 0.16
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.17
% 2.08/1.23  Inferencing          : 0.06
% 2.08/1.23  Reduction            : 0.05
% 2.08/1.23  Demodulation         : 0.04
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.03
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.49
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
