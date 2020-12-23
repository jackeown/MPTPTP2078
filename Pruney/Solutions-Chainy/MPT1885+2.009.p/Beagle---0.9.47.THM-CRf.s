%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 128 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 586 expanded)
%              Number of equality atoms :    9 (  55 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v3_tex_2(C,A)
                <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( ~ v2_struct_0('#skF_1'(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | v1_xboole_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_28])).

tff(c_34,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_31])).

tff(c_35,plain,(
    ~ v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_34])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( v1_pre_topc('#skF_1'(A_22,B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | v1_xboole_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,
    ( v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_42,plain,
    ( v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_39])).

tff(c_43,plain,(
    v1_pre_topc('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_42])).

tff(c_44,plain,(
    ! [A_24,B_25] :
      ( m1_pre_topc('#skF_1'(A_24,B_25),A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_49,plain,
    ( m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_50,plain,(
    m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_49])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( u1_struct_0('#skF_1'(A_26,B_27)) = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | v1_xboole_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_57,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_58,plain,(
    u1_struct_0('#skF_1'('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_57])).

tff(c_16,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    ! [B_28,A_29] :
      ( v4_tex_2(B_28,A_29)
      | ~ v3_tex_2(u1_struct_0(B_28),A_29)
      | ~ m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_28,A_29)
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [A_29] :
      ( v4_tex_2('#skF_1'('#skF_2','#skF_3'),A_29)
      | ~ v3_tex_2(u1_struct_0('#skF_1'('#skF_2','#skF_3')),A_29)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_29)
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_78])).

tff(c_97,plain,(
    ! [A_32] :
      ( v4_tex_2('#skF_1'('#skF_2','#skF_3'),A_32)
      | ~ v3_tex_2('#skF_3',A_32)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),A_32)
      | ~ l1_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_103,plain,
    ( v4_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_107,plain,
    ( v4_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_50,c_16,c_103])).

tff(c_108,plain,(
    v4_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_107])).

tff(c_14,plain,(
    ! [C_18] :
      ( u1_struct_0(C_18) != '#skF_3'
      | ~ v4_tex_2(C_18,'#skF_2')
      | ~ m1_pre_topc(C_18,'#skF_2')
      | ~ v1_pre_topc(C_18)
      | v2_struct_0(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_111,plain,
    ( u1_struct_0('#skF_1'('#skF_2','#skF_3')) != '#skF_3'
    | ~ m1_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_pre_topc('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_114,plain,(
    v2_struct_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_50,c_58,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 1.91/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.91/1.21  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.21  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.91/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.91/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.91/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.21  
% 2.05/1.22  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tex_2)).
% 2.05/1.22  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.05/1.22  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v3_tex_2(C, A) <=> v4_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_tex_2)).
% 2.05/1.22  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_20, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_28, plain, (![A_20, B_21]: (~v2_struct_0('#skF_1'(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | v1_xboole_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_31, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_28])).
% 2.05/1.22  tff(c_34, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_31])).
% 2.05/1.22  tff(c_35, plain, (~v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_34])).
% 2.05/1.22  tff(c_36, plain, (![A_22, B_23]: (v1_pre_topc('#skF_1'(A_22, B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | v1_xboole_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_39, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.05/1.22  tff(c_42, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39])).
% 2.05/1.22  tff(c_43, plain, (v1_pre_topc('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_42])).
% 2.05/1.22  tff(c_44, plain, (![A_24, B_25]: (m1_pre_topc('#skF_1'(A_24, B_25), A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_46, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_44])).
% 2.05/1.22  tff(c_49, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 2.05/1.22  tff(c_50, plain, (m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_49])).
% 2.05/1.22  tff(c_51, plain, (![A_26, B_27]: (u1_struct_0('#skF_1'(A_26, B_27))=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | v1_xboole_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.22  tff(c_54, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_51])).
% 2.05/1.22  tff(c_57, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3' | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_54])).
% 2.05/1.22  tff(c_58, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_57])).
% 2.05/1.22  tff(c_16, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_78, plain, (![B_28, A_29]: (v4_tex_2(B_28, A_29) | ~v3_tex_2(u1_struct_0(B_28), A_29) | ~m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_28, A_29) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.22  tff(c_81, plain, (![A_29]: (v4_tex_2('#skF_1'('#skF_2', '#skF_3'), A_29) | ~v3_tex_2(u1_struct_0('#skF_1'('#skF_2', '#skF_3')), A_29) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_29) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(superposition, [status(thm), theory('equality')], [c_58, c_78])).
% 2.05/1.22  tff(c_97, plain, (![A_32]: (v4_tex_2('#skF_1'('#skF_2', '#skF_3'), A_32) | ~v3_tex_2('#skF_3', A_32) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_32) | ~l1_pre_topc(A_32) | v2_struct_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_81])).
% 2.05/1.22  tff(c_103, plain, (v4_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_97])).
% 2.05/1.22  tff(c_107, plain, (v4_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_50, c_16, c_103])).
% 2.05/1.22  tff(c_108, plain, (v4_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_107])).
% 2.05/1.22  tff(c_14, plain, (![C_18]: (u1_struct_0(C_18)!='#skF_3' | ~v4_tex_2(C_18, '#skF_2') | ~m1_pre_topc(C_18, '#skF_2') | ~v1_pre_topc(C_18) | v2_struct_0(C_18))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.05/1.22  tff(c_111, plain, (u1_struct_0('#skF_1'('#skF_2', '#skF_3'))!='#skF_3' | ~m1_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v1_pre_topc('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_108, c_14])).
% 2.05/1.22  tff(c_114, plain, (v2_struct_0('#skF_1'('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_50, c_58, c_111])).
% 2.05/1.22  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_114])).
% 2.05/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  Inference rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Ref     : 0
% 2.05/1.22  #Sup     : 17
% 2.05/1.22  #Fact    : 0
% 2.05/1.22  #Define  : 0
% 2.05/1.22  #Split   : 1
% 2.05/1.22  #Chain   : 0
% 2.05/1.22  #Close   : 0
% 2.05/1.22  
% 2.05/1.22  Ordering : KBO
% 2.05/1.22  
% 2.05/1.22  Simplification rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Subsume      : 5
% 2.05/1.22  #Demod        : 12
% 2.05/1.22  #Tautology    : 2
% 2.05/1.22  #SimpNegUnit  : 13
% 2.05/1.22  #BackRed      : 0
% 2.05/1.22  
% 2.05/1.22  #Partial instantiations: 0
% 2.05/1.22  #Strategies tried      : 1
% 2.05/1.22  
% 2.05/1.22  Timing (in seconds)
% 2.05/1.22  ----------------------
% 2.05/1.23  Preprocessing        : 0.28
% 2.05/1.23  Parsing              : 0.15
% 2.05/1.23  CNF conversion       : 0.02
% 2.05/1.23  Main loop            : 0.15
% 2.05/1.23  Inferencing          : 0.05
% 2.05/1.23  Reduction            : 0.04
% 2.05/1.23  Demodulation         : 0.03
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.03
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.45
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
