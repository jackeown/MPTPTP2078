%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:56 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   44 (  92 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 244 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_69,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_pre_topc(A_4,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [B_26,A_27] :
      ( m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_13,A_12] :
      ( v1_subset_1(B_13,A_12)
      | B_13 = A_12
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [B_26,A_27] :
      ( v1_subset_1(u1_struct_0(B_26),u1_struct_0(A_27))
      | u1_struct_0(B_26) = u1_struct_0(A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_8])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [B_36,A_37] :
      ( v1_tex_2(B_36,A_37)
      | ~ v1_subset_1(u1_struct_0(B_36),u1_struct_0(A_37))
      | ~ m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    ! [B_41,A_42] :
      ( v1_tex_2(B_41,A_42)
      | ~ v1_subset_1(u1_struct_0(B_41),u1_struct_0(A_42))
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_58])).

tff(c_81,plain,(
    ! [B_43,A_44] :
      ( v1_tex_2(B_43,A_44)
      | u1_struct_0(B_43) = u1_struct_0(A_44)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_20,plain,(
    ~ v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_88,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_20])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_88])).

tff(c_63,plain,(
    ! [C_38,B_39,A_40] :
      ( g1_pre_topc(u1_struct_0(C_38),u1_pre_topc(C_38)) = g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39))
      | u1_struct_0(C_38) != u1_struct_0(B_39)
      | ~ m1_pre_topc(C_38,A_40)
      | ~ m1_pre_topc(B_39,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [B_39] :
      ( g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | u1_struct_0(B_39) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_71,plain,(
    ! [B_39] :
      ( g1_pre_topc(u1_struct_0(B_39),u1_pre_topc(B_39)) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | u1_struct_0(B_39) != u1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_67])).

tff(c_150,plain,(
    ! [B_46] :
      ( g1_pre_topc(u1_struct_0(B_46),u1_pre_topc(B_46)) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_2'))
      | u1_struct_0(B_46) != u1_struct_0('#skF_1')
      | ~ m1_pre_topc(B_46,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_71])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_94,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_2')) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_16])).

tff(c_155,plain,(
    ! [B_46] :
      ( g1_pre_topc(u1_struct_0(B_46),u1_pre_topc(B_46)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | u1_struct_0(B_46) != u1_struct_0('#skF_1')
      | ~ m1_pre_topc(B_46,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_94])).

tff(c_194,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_155])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:09:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.22  
% 2.08/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.23  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.08/1.23  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.08/1.23  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.08/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.08/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  
% 2.27/1.24  tff(f_83, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_tex_2(B, A) & m1_pre_topc(B, A)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tex_2)).
% 2.27/1.24  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.27/1.24  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.27/1.24  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.27/1.24  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.27/1.24  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => ((u1_struct_0(B) = u1_struct_0(C)) => (g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tsep_1)).
% 2.27/1.24  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.24  tff(c_4, plain, (![A_4]: (m1_pre_topc(A_4, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.24  tff(c_18, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.24  tff(c_28, plain, (![B_26, A_27]: (m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.24  tff(c_8, plain, (![B_13, A_12]: (v1_subset_1(B_13, A_12) | B_13=A_12 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.24  tff(c_36, plain, (![B_26, A_27]: (v1_subset_1(u1_struct_0(B_26), u1_struct_0(A_27)) | u1_struct_0(B_26)=u1_struct_0(A_27) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_28, c_8])).
% 2.27/1.24  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.24  tff(c_58, plain, (![B_36, A_37]: (v1_tex_2(B_36, A_37) | ~v1_subset_1(u1_struct_0(B_36), u1_struct_0(A_37)) | ~m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.27/1.24  tff(c_72, plain, (![B_41, A_42]: (v1_tex_2(B_41, A_42) | ~v1_subset_1(u1_struct_0(B_41), u1_struct_0(A_42)) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_2, c_58])).
% 2.27/1.24  tff(c_81, plain, (![B_43, A_44]: (v1_tex_2(B_43, A_44) | u1_struct_0(B_43)=u1_struct_0(A_44) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_36, c_72])).
% 2.27/1.24  tff(c_20, plain, (~v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.24  tff(c_88, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_81, c_20])).
% 2.27/1.24  tff(c_93, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_88])).
% 2.27/1.24  tff(c_63, plain, (![C_38, B_39, A_40]: (g1_pre_topc(u1_struct_0(C_38), u1_pre_topc(C_38))=g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39)) | u1_struct_0(C_38)!=u1_struct_0(B_39) | ~m1_pre_topc(C_38, A_40) | ~m1_pre_topc(B_39, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.24  tff(c_67, plain, (![B_39]: (g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | u1_struct_0(B_39)!=u1_struct_0('#skF_2') | ~m1_pre_topc(B_39, '#skF_1') | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.27/1.24  tff(c_71, plain, (![B_39]: (g1_pre_topc(u1_struct_0(B_39), u1_pre_topc(B_39))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | u1_struct_0(B_39)!=u1_struct_0('#skF_2') | ~m1_pre_topc(B_39, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_67])).
% 2.27/1.24  tff(c_150, plain, (![B_46]: (g1_pre_topc(u1_struct_0(B_46), u1_pre_topc(B_46))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_2')) | u1_struct_0(B_46)!=u1_struct_0('#skF_1') | ~m1_pre_topc(B_46, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_71])).
% 2.27/1.24  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.27/1.24  tff(c_94, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_2'))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_16])).
% 2.27/1.24  tff(c_155, plain, (![B_46]: (g1_pre_topc(u1_struct_0(B_46), u1_pre_topc(B_46))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | u1_struct_0(B_46)!=u1_struct_0('#skF_1') | ~m1_pre_topc(B_46, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_94])).
% 2.27/1.24  tff(c_194, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_155])).
% 2.27/1.24  tff(c_206, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4, c_194])).
% 2.27/1.24  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_206])).
% 2.27/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  Inference rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Ref     : 1
% 2.27/1.24  #Sup     : 39
% 2.27/1.24  #Fact    : 0
% 2.27/1.24  #Define  : 0
% 2.27/1.24  #Split   : 2
% 2.27/1.24  #Chain   : 0
% 2.27/1.24  #Close   : 0
% 2.27/1.24  
% 2.27/1.24  Ordering : KBO
% 2.27/1.24  
% 2.27/1.24  Simplification rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Subsume      : 7
% 2.27/1.24  #Demod        : 20
% 2.27/1.24  #Tautology    : 9
% 2.27/1.24  #SimpNegUnit  : 0
% 2.27/1.24  #BackRed      : 1
% 2.27/1.24  
% 2.27/1.24  #Partial instantiations: 0
% 2.27/1.24  #Strategies tried      : 1
% 2.27/1.24  
% 2.27/1.24  Timing (in seconds)
% 2.27/1.24  ----------------------
% 2.27/1.24  Preprocessing        : 0.29
% 2.27/1.24  Parsing              : 0.15
% 2.27/1.24  CNF conversion       : 0.02
% 2.27/1.24  Main loop            : 0.18
% 2.27/1.24  Inferencing          : 0.07
% 2.27/1.24  Reduction            : 0.05
% 2.27/1.24  Demodulation         : 0.04
% 2.27/1.24  BG Simplification    : 0.01
% 2.27/1.24  Subsumption          : 0.04
% 2.27/1.24  Abstraction          : 0.01
% 2.27/1.24  MUC search           : 0.00
% 2.27/1.24  Cooper               : 0.00
% 2.27/1.24  Total                : 0.50
% 2.27/1.24  Index Insertion      : 0.00
% 2.27/1.24  Index Deletion       : 0.00
% 2.27/1.24  Index Matching       : 0.00
% 2.27/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
