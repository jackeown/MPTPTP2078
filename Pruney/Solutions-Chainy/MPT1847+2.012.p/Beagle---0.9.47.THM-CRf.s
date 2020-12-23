%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 142 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(c_16,plain,(
    ~ v1_tex_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_27,plain,(
    ! [B_25,A_26] :
      ( l1_pre_topc(B_25)
      | ~ m1_pre_topc(B_25,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_59,plain,(
    ! [C_34,A_35,D_36,B_37] :
      ( C_34 = A_35
      | g1_pre_topc(C_34,D_36) != g1_pre_topc(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [A_40,B_41] :
      ( u1_struct_0('#skF_2') = A_40
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_73,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_82,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_73])).

tff(c_84,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_82])).

tff(c_10,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_151,plain,(
    ! [B_49,A_50] :
      ( v1_subset_1(u1_struct_0(B_49),u1_struct_0(A_50))
      | ~ v1_tex_2(B_49,A_50)
      | ~ m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_179,plain,(
    ! [B_52,A_53] :
      ( v1_subset_1(u1_struct_0(B_52),u1_struct_0(A_53))
      | ~ v1_tex_2(B_52,A_53)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_255,plain,(
    ! [A_63] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_63))
      | ~ v1_tex_2('#skF_2',A_63)
      | ~ m1_pre_topc('#skF_2',A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_179])).

tff(c_74,plain,(
    ! [B_42,A_43] :
      ( v1_tex_2(B_42,A_43)
      | ~ v1_subset_1(u1_struct_0(B_42),u1_struct_0(A_43))
      | ~ m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [B_13,A_11] :
      ( v1_tex_2(B_13,A_11)
      | ~ v1_subset_1(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_317,plain,(
    ! [A_66] :
      ( v1_tex_2('#skF_3',A_66)
      | ~ m1_pre_topc('#skF_3',A_66)
      | ~ v1_tex_2('#skF_2',A_66)
      | ~ m1_pre_topc('#skF_2',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_255,c_78])).

tff(c_324,plain,
    ( v1_tex_2('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_317])).

tff(c_330,plain,(
    v1_tex_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_324])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.36  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.36  
% 2.36/1.36  %Foreground sorts:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Background operators:
% 2.36/1.36  
% 2.36/1.36  
% 2.36/1.36  %Foreground operators:
% 2.36/1.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.36  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.36/1.36  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.36/1.36  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.36/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.36/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.36  
% 2.36/1.37  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 2.36/1.37  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.36/1.37  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.36/1.37  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.36/1.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.36/1.37  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 2.36/1.37  tff(c_16, plain, (~v1_tex_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_18, plain, (v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_27, plain, (![B_25, A_26]: (l1_pre_topc(B_25) | ~m1_pre_topc(B_25, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.37  tff(c_30, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_27])).
% 2.36/1.37  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.36/1.37  tff(c_4, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.37  tff(c_20, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.37  tff(c_59, plain, (![C_34, A_35, D_36, B_37]: (C_34=A_35 | g1_pre_topc(C_34, D_36)!=g1_pre_topc(A_35, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.37  tff(c_69, plain, (![A_40, B_41]: (u1_struct_0('#skF_2')=A_40 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 2.36/1.37  tff(c_73, plain, (![A_4]: (u1_struct_0(A_4)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_4, c_69])).
% 2.36/1.37  tff(c_82, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_73])).
% 2.36/1.37  tff(c_84, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_82])).
% 2.36/1.37  tff(c_10, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.36/1.37  tff(c_151, plain, (![B_49, A_50]: (v1_subset_1(u1_struct_0(B_49), u1_struct_0(A_50)) | ~v1_tex_2(B_49, A_50) | ~m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.37  tff(c_179, plain, (![B_52, A_53]: (v1_subset_1(u1_struct_0(B_52), u1_struct_0(A_53)) | ~v1_tex_2(B_52, A_53) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_10, c_151])).
% 2.36/1.37  tff(c_255, plain, (![A_63]: (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0(A_63)) | ~v1_tex_2('#skF_2', A_63) | ~m1_pre_topc('#skF_2', A_63) | ~l1_pre_topc(A_63))), inference(superposition, [status(thm), theory('equality')], [c_84, c_179])).
% 2.36/1.37  tff(c_74, plain, (![B_42, A_43]: (v1_tex_2(B_42, A_43) | ~v1_subset_1(u1_struct_0(B_42), u1_struct_0(A_43)) | ~m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.37  tff(c_78, plain, (![B_13, A_11]: (v1_tex_2(B_13, A_11) | ~v1_subset_1(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_10, c_74])).
% 2.36/1.37  tff(c_317, plain, (![A_66]: (v1_tex_2('#skF_3', A_66) | ~m1_pre_topc('#skF_3', A_66) | ~v1_tex_2('#skF_2', A_66) | ~m1_pre_topc('#skF_2', A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_255, c_78])).
% 2.36/1.37  tff(c_324, plain, (v1_tex_2('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_317])).
% 2.36/1.37  tff(c_330, plain, (v1_tex_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_324])).
% 2.36/1.37  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_330])).
% 2.36/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.37  
% 2.36/1.37  Inference rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Ref     : 6
% 2.36/1.37  #Sup     : 59
% 2.36/1.37  #Fact    : 0
% 2.36/1.37  #Define  : 0
% 2.36/1.37  #Split   : 2
% 2.36/1.37  #Chain   : 0
% 2.36/1.37  #Close   : 0
% 2.36/1.37  
% 2.36/1.37  Ordering : KBO
% 2.36/1.37  
% 2.36/1.37  Simplification rules
% 2.36/1.37  ----------------------
% 2.36/1.37  #Subsume      : 17
% 2.36/1.37  #Demod        : 42
% 2.36/1.37  #Tautology    : 22
% 2.36/1.37  #SimpNegUnit  : 1
% 2.36/1.37  #BackRed      : 5
% 2.36/1.37  
% 2.36/1.37  #Partial instantiations: 0
% 2.36/1.37  #Strategies tried      : 1
% 2.36/1.37  
% 2.36/1.37  Timing (in seconds)
% 2.36/1.37  ----------------------
% 2.36/1.38  Preprocessing        : 0.34
% 2.36/1.38  Parsing              : 0.19
% 2.36/1.38  CNF conversion       : 0.02
% 2.36/1.38  Main loop            : 0.24
% 2.36/1.38  Inferencing          : 0.09
% 2.36/1.38  Reduction            : 0.07
% 2.36/1.38  Demodulation         : 0.05
% 2.36/1.38  BG Simplification    : 0.01
% 2.36/1.38  Subsumption          : 0.06
% 2.36/1.38  Abstraction          : 0.01
% 2.36/1.38  MUC search           : 0.00
% 2.36/1.38  Cooper               : 0.00
% 2.36/1.38  Total                : 0.62
% 2.36/1.38  Index Insertion      : 0.00
% 2.36/1.38  Index Deletion       : 0.00
% 2.36/1.38  Index Matching       : 0.00
% 2.36/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
