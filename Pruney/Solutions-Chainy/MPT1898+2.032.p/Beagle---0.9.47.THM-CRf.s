%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:34 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 119 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 378 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_xboole_0('#skF_1'(A_1))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [B_17,A_18] :
      ( v2_tex_2(B_17,A_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v1_xboole_0(B_17)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    ! [A_1] :
      ( v2_tex_2('#skF_1'(A_1),A_1)
      | ~ v1_xboole_0('#skF_1'(A_1))
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_33])).

tff(c_49,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1('#skF_2'(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ v2_tex_2(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v3_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [B_13] :
      ( ~ v3_tex_2(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_60,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_49,c_14])).

tff(c_66,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_60])).

tff(c_68,plain,(
    ! [B_28] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_28),'#skF_3')
      | ~ v2_tex_2(B_28,'#skF_3')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_66])).

tff(c_76,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'('#skF_3')),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_83,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'('#skF_3')),'#skF_3')
    | ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_84,plain,(
    ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_84])).

tff(c_90,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_87])).

tff(c_91,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_90])).

tff(c_94,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_91])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_94])).

tff(c_100,plain,(
    v2_tex_2('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( v3_tex_2('#skF_2'(A_23,B_24),A_23)
      | ~ v2_tex_2(B_24,A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v3_tdlat_3(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_47,plain,(
    ! [A_1] :
      ( v3_tex_2('#skF_2'(A_1,'#skF_1'(A_1)),A_1)
      | ~ v2_tex_2('#skF_1'(A_1),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_44])).

tff(c_99,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_104,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_99])).

tff(c_107,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20,c_18,c_100,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 1.94/1.22  
% 1.94/1.22  %Foreground sorts:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Background operators:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Foreground operators:
% 1.94/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.94/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.22  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.94/1.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.94/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.22  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.94/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.94/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.22  
% 2.02/1.23  tff(f_84, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 2.02/1.23  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_connsp_1)).
% 2.02/1.23  tff(f_46, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.02/1.23  tff(f_69, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 2.02/1.23  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_16, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_20, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_18, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.23  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.23  tff(c_33, plain, (![B_17, A_18]: (v2_tex_2(B_17, A_18) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_18))) | ~v1_xboole_0(B_17) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.23  tff(c_37, plain, (![A_1]: (v2_tex_2('#skF_1'(A_1), A_1) | ~v1_xboole_0('#skF_1'(A_1)) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_4, c_33])).
% 2.02/1.23  tff(c_49, plain, (![A_26, B_27]: (m1_subset_1('#skF_2'(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~v2_tex_2(B_27, A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v3_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.23  tff(c_14, plain, (![B_13]: (~v3_tex_2(B_13, '#skF_3') | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.23  tff(c_60, plain, (![B_27]: (~v3_tex_2('#skF_2'('#skF_3', B_27), '#skF_3') | ~v2_tex_2(B_27, '#skF_3') | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_49, c_14])).
% 2.02/1.23  tff(c_66, plain, (![B_27]: (~v3_tex_2('#skF_2'('#skF_3', B_27), '#skF_3') | ~v2_tex_2(B_27, '#skF_3') | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_60])).
% 2.02/1.23  tff(c_68, plain, (![B_28]: (~v3_tex_2('#skF_2'('#skF_3', B_28), '#skF_3') | ~v2_tex_2(B_28, '#skF_3') | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_66])).
% 2.02/1.23  tff(c_76, plain, (~v3_tex_2('#skF_2'('#skF_3', '#skF_1'('#skF_3')), '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.02/1.23  tff(c_83, plain, (~v3_tex_2('#skF_2'('#skF_3', '#skF_1'('#skF_3')), '#skF_3') | ~v2_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_76])).
% 2.02/1.23  tff(c_84, plain, (~v2_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_83])).
% 2.02/1.23  tff(c_87, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_84])).
% 2.02/1.23  tff(c_90, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_87])).
% 2.02/1.23  tff(c_91, plain, (~v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22, c_90])).
% 2.02/1.23  tff(c_94, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_91])).
% 2.02/1.23  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_94])).
% 2.02/1.23  tff(c_100, plain, (v2_tex_2('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_83])).
% 2.02/1.23  tff(c_44, plain, (![A_23, B_24]: (v3_tex_2('#skF_2'(A_23, B_24), A_23) | ~v2_tex_2(B_24, A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v3_tdlat_3(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.23  tff(c_47, plain, (![A_1]: (v3_tex_2('#skF_2'(A_1, '#skF_1'(A_1)), A_1) | ~v2_tex_2('#skF_1'(A_1), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_4, c_44])).
% 2.02/1.23  tff(c_99, plain, (~v3_tex_2('#skF_2'('#skF_3', '#skF_1'('#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_83])).
% 2.02/1.23  tff(c_104, plain, (~v2_tex_2('#skF_1'('#skF_3'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_47, c_99])).
% 2.02/1.23  tff(c_107, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20, c_18, c_100, c_104])).
% 2.02/1.23  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_107])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 13
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 1
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 0
% 2.02/1.23  #Demod        : 15
% 2.02/1.23  #Tautology    : 0
% 2.02/1.23  #SimpNegUnit  : 4
% 2.02/1.23  #BackRed      : 0
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.24  Preprocessing        : 0.29
% 2.02/1.24  Parsing              : 0.16
% 2.02/1.24  CNF conversion       : 0.02
% 2.02/1.24  Main loop            : 0.15
% 2.02/1.24  Inferencing          : 0.07
% 2.02/1.24  Reduction            : 0.04
% 2.02/1.24  Demodulation         : 0.03
% 2.02/1.24  BG Simplification    : 0.01
% 2.02/1.24  Subsumption          : 0.03
% 2.02/1.24  Abstraction          : 0.01
% 2.02/1.24  MUC search           : 0.00
% 2.02/1.24  Cooper               : 0.00
% 2.02/1.24  Total                : 0.47
% 2.02/1.24  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
