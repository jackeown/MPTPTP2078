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
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 124 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   93 ( 353 expanded)
%              Number of equality atoms :   16 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29,plain,(
    ! [B_25,A_26] :
      ( l1_pre_topc(B_25)
      | ~ m1_pre_topc(B_25,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_65,plain,(
    ! [B_36,A_37] :
      ( u1_struct_0(B_36) = '#skF_1'(A_37,B_36)
      | v1_tex_2(B_36,A_37)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_18])).

tff(c_71,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_68])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_80,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76])).

tff(c_22,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    ! [C_32,A_33,D_34,B_35] :
      ( C_32 = A_33
      | g1_pre_topc(C_32,D_34) != g1_pre_topc(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [A_33,B_35] :
      ( u1_struct_0('#skF_3') = A_33
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_108,plain,(
    ! [A_43,B_44] :
      ( u1_struct_0('#skF_3') = A_43
      | g1_pre_topc(A_43,B_44) != g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_62])).

tff(c_115,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_108])).

tff(c_176,plain,(
    ! [B_47,A_48] :
      ( v1_subset_1(u1_struct_0(B_47),u1_struct_0(A_48))
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v1_tex_2(B_47,A_48)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    ! [A_48] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_48))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v1_tex_2('#skF_3',A_48)
      | ~ m1_pre_topc('#skF_3',A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_176])).

tff(c_260,plain,(
    ! [A_59] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_59))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ v1_tex_2('#skF_3',A_59)
      | ~ m1_pre_topc('#skF_3',A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_179])).

tff(c_267,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_275,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_26,c_20,c_267])).

tff(c_276,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_275])).

tff(c_12,plain,(
    ! [A_11,B_17] :
      ( ~ v1_subset_1('#skF_1'(A_11,B_17),u1_struct_0(A_11))
      | v1_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_281,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_276,c_12])).

tff(c_284,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.35  
% 2.25/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.25/1.36  
% 2.25/1.36  %Foreground sorts:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Background operators:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Foreground operators:
% 2.25/1.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.36  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.25/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.25/1.36  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.25/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.25/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.25/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.25/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.36  
% 2.45/1.37  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 2.45/1.37  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.45/1.37  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.45/1.37  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.45/1.37  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.45/1.37  tff(c_18, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_20, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_16, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v1_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.37  tff(c_29, plain, (![B_25, A_26]: (l1_pre_topc(B_25) | ~m1_pre_topc(B_25, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.37  tff(c_32, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_29])).
% 2.45/1.37  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.45/1.37  tff(c_65, plain, (![B_36, A_37]: (u1_struct_0(B_36)='#skF_1'(A_37, B_36) | v1_tex_2(B_36, A_37) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.37  tff(c_68, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_65, c_18])).
% 2.45/1.37  tff(c_71, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_68])).
% 2.45/1.37  tff(c_4, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.37  tff(c_76, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 2.45/1.37  tff(c_80, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_76])).
% 2.45/1.37  tff(c_22, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.37  tff(c_60, plain, (![C_32, A_33, D_34, B_35]: (C_32=A_33 | g1_pre_topc(C_32, D_34)!=g1_pre_topc(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.37  tff(c_62, plain, (![A_33, B_35]: (u1_struct_0('#skF_3')=A_33 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(superposition, [status(thm), theory('equality')], [c_22, c_60])).
% 2.45/1.37  tff(c_108, plain, (![A_43, B_44]: (u1_struct_0('#skF_3')=A_43 | g1_pre_topc(A_43, B_44)!=g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4')) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_62])).
% 2.45/1.37  tff(c_115, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_108])).
% 2.45/1.37  tff(c_176, plain, (![B_47, A_48]: (v1_subset_1(u1_struct_0(B_47), u1_struct_0(A_48)) | ~m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_48))) | ~v1_tex_2(B_47, A_48) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.37  tff(c_179, plain, (![A_48]: (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0(A_48)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_48))) | ~v1_tex_2('#skF_3', A_48) | ~m1_pre_topc('#skF_3', A_48) | ~l1_pre_topc(A_48))), inference(superposition, [status(thm), theory('equality')], [c_115, c_176])).
% 2.45/1.37  tff(c_260, plain, (![A_59]: (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_59)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_59))) | ~v1_tex_2('#skF_3', A_59) | ~m1_pre_topc('#skF_3', A_59) | ~l1_pre_topc(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_179])).
% 2.45/1.37  tff(c_267, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_260])).
% 2.45/1.37  tff(c_275, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_26, c_20, c_267])).
% 2.45/1.37  tff(c_276, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_275])).
% 2.45/1.37  tff(c_12, plain, (![A_11, B_17]: (~v1_subset_1('#skF_1'(A_11, B_17), u1_struct_0(A_11)) | v1_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.37  tff(c_281, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_276, c_12])).
% 2.45/1.37  tff(c_284, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_281])).
% 2.45/1.37  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_284])).
% 2.45/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  Inference rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Ref     : 5
% 2.45/1.37  #Sup     : 52
% 2.45/1.37  #Fact    : 0
% 2.45/1.37  #Define  : 0
% 2.45/1.37  #Split   : 2
% 2.45/1.37  #Chain   : 0
% 2.45/1.37  #Close   : 0
% 2.45/1.37  
% 2.45/1.37  Ordering : KBO
% 2.45/1.37  
% 2.45/1.37  Simplification rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Subsume      : 14
% 2.45/1.37  #Demod        : 73
% 2.45/1.37  #Tautology    : 20
% 2.45/1.37  #SimpNegUnit  : 3
% 2.45/1.37  #BackRed      : 5
% 2.45/1.37  
% 2.45/1.37  #Partial instantiations: 0
% 2.45/1.37  #Strategies tried      : 1
% 2.45/1.37  
% 2.45/1.37  Timing (in seconds)
% 2.45/1.37  ----------------------
% 2.45/1.37  Preprocessing        : 0.31
% 2.45/1.37  Parsing              : 0.17
% 2.45/1.37  CNF conversion       : 0.02
% 2.45/1.38  Main loop            : 0.23
% 2.45/1.38  Inferencing          : 0.08
% 2.45/1.38  Reduction            : 0.08
% 2.45/1.38  Demodulation         : 0.05
% 2.45/1.38  BG Simplification    : 0.01
% 2.45/1.38  Subsumption          : 0.05
% 2.45/1.38  Abstraction          : 0.01
% 2.45/1.38  MUC search           : 0.00
% 2.45/1.38  Cooper               : 0.00
% 2.45/1.38  Total                : 0.58
% 2.45/1.38  Index Insertion      : 0.00
% 2.45/1.38  Index Deletion       : 0.00
% 2.45/1.38  Index Matching       : 0.00
% 2.45/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
