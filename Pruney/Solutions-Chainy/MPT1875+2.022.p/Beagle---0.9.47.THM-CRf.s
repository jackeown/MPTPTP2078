%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   52 (  84 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 203 expanded)
%              Number of equality atoms :    3 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    ! [A_14] :
      ( v2_tex_2(u1_struct_0(A_14),A_14)
      | ~ v1_tdlat_3(A_14)
      | ~ m1_subset_1(u1_struct_0(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    ! [A_14] :
      ( v2_tex_2(u1_struct_0(A_14),A_14)
      | ~ v1_tdlat_3(A_14)
      | ~ l1_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_14])).

tff(c_20,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_1'(A_35,B_36,C_37),B_36)
      | r1_tarski(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [A_47,B_48,C_49,A_50] :
      ( r2_hidden('#skF_1'(A_47,B_48,C_49),A_50)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_50))
      | r1_tarski(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_54,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8,C_12),C_12)
      | r1_tarski(B_8,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [B_51,A_52,A_53] :
      ( ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | r1_tarski(B_51,A_52)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_103,plain,(
    ! [A_53] :
      ( r1_tarski('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(A_53))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_107,plain,(
    ! [A_54] :
      ( ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(A_54))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_54)) ) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_111,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_31,c_107])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_111])).

tff(c_116,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_18,plain,(
    ! [C_23,A_17,B_21] :
      ( v2_tex_2(C_23,A_17)
      | ~ v2_tex_2(B_21,A_17)
      | ~ r1_tarski(C_23,B_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_120,plain,(
    ! [A_55] :
      ( v2_tex_2('#skF_3',A_55)
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_55)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_124,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_120])).

tff(c_127,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_124])).

tff(c_128,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_127])).

tff(c_131,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_33,c_128])).

tff(c_134,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.28  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.00/1.28  
% 2.00/1.28  %Foreground sorts:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Background operators:
% 2.00/1.28  
% 2.00/1.28  
% 2.00/1.28  %Foreground operators:
% 2.00/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.00/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.00/1.28  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.00/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.00/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.00/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.00/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.28  
% 2.00/1.30  tff(f_93, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.00/1.30  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.00/1.30  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.00/1.30  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.00/1.30  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.00/1.30  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.00/1.30  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.00/1.30  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.30  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.30  tff(c_26, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.30  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.30  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.30  tff(c_31, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.00/1.30  tff(c_14, plain, (![A_14]: (v2_tex_2(u1_struct_0(A_14), A_14) | ~v1_tdlat_3(A_14) | ~m1_subset_1(u1_struct_0(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.30  tff(c_33, plain, (![A_14]: (v2_tex_2(u1_struct_0(A_14), A_14) | ~v1_tdlat_3(A_14) | ~l1_pre_topc(A_14) | v2_struct_0(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_14])).
% 2.00/1.30  tff(c_20, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.30  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.30  tff(c_54, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_1'(A_35, B_36, C_37), B_36) | r1_tarski(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.30  tff(c_6, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.30  tff(c_85, plain, (![A_47, B_48, C_49, A_50]: (r2_hidden('#skF_1'(A_47, B_48, C_49), A_50) | ~m1_subset_1(B_48, k1_zfmisc_1(A_50)) | r1_tarski(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_54, c_6])).
% 2.00/1.30  tff(c_8, plain, (![A_7, B_8, C_12]: (~r2_hidden('#skF_1'(A_7, B_8, C_12), C_12) | r1_tarski(B_8, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.30  tff(c_94, plain, (![B_51, A_52, A_53]: (~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | r1_tarski(B_51, A_52) | ~m1_subset_1(A_52, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_85, c_8])).
% 2.00/1.30  tff(c_103, plain, (![A_53]: (r1_tarski('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(A_53)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_22, c_94])).
% 2.00/1.30  tff(c_107, plain, (![A_54]: (~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(A_54)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_54)))), inference(splitLeft, [status(thm)], [c_103])).
% 2.00/1.30  tff(c_111, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_31, c_107])).
% 2.00/1.30  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_111])).
% 2.00/1.30  tff(c_116, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_103])).
% 2.00/1.30  tff(c_18, plain, (![C_23, A_17, B_21]: (v2_tex_2(C_23, A_17) | ~v2_tex_2(B_21, A_17) | ~r1_tarski(C_23, B_21) | ~m1_subset_1(C_23, k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.30  tff(c_120, plain, (![A_55]: (v2_tex_2('#skF_3', A_55) | ~v2_tex_2(u1_struct_0('#skF_2'), A_55) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_116, c_18])).
% 2.00/1.30  tff(c_124, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_31, c_120])).
% 2.00/1.30  tff(c_127, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_124])).
% 2.00/1.30  tff(c_128, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_20, c_127])).
% 2.00/1.30  tff(c_131, plain, (~v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_33, c_128])).
% 2.00/1.30  tff(c_134, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_131])).
% 2.00/1.30  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_134])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 19
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 1
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 0
% 2.00/1.30  #Demod        : 11
% 2.00/1.30  #Tautology    : 8
% 2.00/1.30  #SimpNegUnit  : 2
% 2.00/1.30  #BackRed      : 0
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.31
% 2.00/1.30  Parsing              : 0.17
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.16
% 2.00/1.30  Inferencing          : 0.06
% 2.00/1.30  Reduction            : 0.05
% 2.00/1.30  Demodulation         : 0.03
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.04
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.50
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
