%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 178 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 845 expanded)
%              Number of equality atoms :   20 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_41,plain,(
    ! [A_25,B_26] :
      ( ~ v2_struct_0('#skF_2'(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | v1_xboole_0(B_26)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_41])).

tff(c_47,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_47])).

tff(c_49,plain,(
    ! [A_27,B_28] :
      ( v1_pre_topc('#skF_2'(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | v1_xboole_0(B_28)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_49])).

tff(c_55,plain,
    ( v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_52])).

tff(c_56,plain,(
    v1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_55])).

tff(c_67,plain,(
    ! [A_34,B_35] :
      ( m1_pre_topc('#skF_2'(A_34,B_35),A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | v1_xboole_0(B_35)
      | ~ l1_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_67])).

tff(c_72,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_69])).

tff(c_73,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_72])).

tff(c_59,plain,(
    ! [A_32,B_33] :
      ( u1_struct_0('#skF_2'(A_32,B_33)) = B_33
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | v1_xboole_0(B_33)
      | ~ l1_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_65,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_66,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_65])).

tff(c_20,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [B_23,A_24] :
      ( u1_struct_0(B_23) = '#skF_1'(A_24,B_23)
      | v4_tex_2(B_23,A_24)
      | ~ m1_pre_topc(B_23,A_24)
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [C_21] :
      ( u1_struct_0(C_21) != '#skF_4'
      | ~ v4_tex_2(C_21,'#skF_3')
      | ~ m1_pre_topc(C_21,'#skF_3')
      | ~ v1_pre_topc(C_21)
      | v2_struct_0(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    ! [B_23] :
      ( u1_struct_0(B_23) != '#skF_4'
      | ~ v1_pre_topc(B_23)
      | v2_struct_0(B_23)
      | u1_struct_0(B_23) = '#skF_1'('#skF_3',B_23)
      | ~ m1_pre_topc(B_23,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_18])).

tff(c_39,plain,(
    ! [B_23] :
      ( u1_struct_0(B_23) != '#skF_4'
      | ~ v1_pre_topc(B_23)
      | v2_struct_0(B_23)
      | u1_struct_0(B_23) = '#skF_1'('#skF_3',B_23)
      | ~ m1_pre_topc(B_23,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_40,plain,(
    ! [B_23] :
      ( u1_struct_0(B_23) != '#skF_4'
      | ~ v1_pre_topc(B_23)
      | v2_struct_0(B_23)
      | u1_struct_0(B_23) = '#skF_1'('#skF_3',B_23)
      | ~ m1_pre_topc(B_23,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_39])).

tff(c_95,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) != '#skF_4'
    | ~ v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_73,c_40])).

tff(c_98,plain,
    ( v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | '#skF_1'('#skF_3','#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_56,c_66,c_95])).

tff(c_99,plain,(
    '#skF_1'('#skF_3','#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_98])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_tex_2('#skF_1'(A_1,B_7),A_1)
      | v4_tex_2(B_7,A_1)
      | ~ m1_pre_topc(B_7,A_1)
      | ~ l1_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_103,plain,
    ( ~ v3_tex_2('#skF_4','#skF_3')
    | v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_4])).

tff(c_107,plain,
    ( v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_73,c_20,c_103])).

tff(c_108,plain,(
    v4_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_107])).

tff(c_112,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) != '#skF_4'
    | ~ m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_108,c_18])).

tff(c_115,plain,(
    v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_73,c_66,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:09:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 1.88/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.88/1.17  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.17  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.88/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.17  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.88/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.88/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.17  
% 1.88/1.18  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 1.88/1.18  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 1.88/1.18  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 1.88/1.18  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_24, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_41, plain, (![A_25, B_26]: (~v2_struct_0('#skF_2'(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | v1_xboole_0(B_26) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.18  tff(c_44, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_41])).
% 1.88/1.18  tff(c_47, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_44])).
% 1.88/1.18  tff(c_48, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_47])).
% 1.88/1.18  tff(c_49, plain, (![A_27, B_28]: (v1_pre_topc('#skF_2'(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | v1_xboole_0(B_28) | ~l1_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.18  tff(c_52, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_49])).
% 1.88/1.18  tff(c_55, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_52])).
% 1.88/1.18  tff(c_56, plain, (v1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_55])).
% 1.88/1.18  tff(c_67, plain, (![A_34, B_35]: (m1_pre_topc('#skF_2'(A_34, B_35), A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_34))) | v1_xboole_0(B_35) | ~l1_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.18  tff(c_69, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_67])).
% 1.88/1.18  tff(c_72, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_69])).
% 1.88/1.18  tff(c_73, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_72])).
% 1.88/1.18  tff(c_59, plain, (![A_32, B_33]: (u1_struct_0('#skF_2'(A_32, B_33))=B_33 | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | v1_xboole_0(B_33) | ~l1_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.88/1.18  tff(c_62, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_59])).
% 1.88/1.18  tff(c_65, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 1.88/1.18  tff(c_66, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_65])).
% 1.88/1.18  tff(c_20, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_32, plain, (![B_23, A_24]: (u1_struct_0(B_23)='#skF_1'(A_24, B_23) | v4_tex_2(B_23, A_24) | ~m1_pre_topc(B_23, A_24) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.18  tff(c_18, plain, (![C_21]: (u1_struct_0(C_21)!='#skF_4' | ~v4_tex_2(C_21, '#skF_3') | ~m1_pre_topc(C_21, '#skF_3') | ~v1_pre_topc(C_21) | v2_struct_0(C_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 1.88/1.18  tff(c_36, plain, (![B_23]: (u1_struct_0(B_23)!='#skF_4' | ~v1_pre_topc(B_23) | v2_struct_0(B_23) | u1_struct_0(B_23)='#skF_1'('#skF_3', B_23) | ~m1_pre_topc(B_23, '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_18])).
% 1.88/1.18  tff(c_39, plain, (![B_23]: (u1_struct_0(B_23)!='#skF_4' | ~v1_pre_topc(B_23) | v2_struct_0(B_23) | u1_struct_0(B_23)='#skF_1'('#skF_3', B_23) | ~m1_pre_topc(B_23, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 1.88/1.18  tff(c_40, plain, (![B_23]: (u1_struct_0(B_23)!='#skF_4' | ~v1_pre_topc(B_23) | v2_struct_0(B_23) | u1_struct_0(B_23)='#skF_1'('#skF_3', B_23) | ~m1_pre_topc(B_23, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_39])).
% 1.88/1.18  tff(c_95, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))!='#skF_4' | ~v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_73, c_40])).
% 1.88/1.18  tff(c_98, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | '#skF_1'('#skF_3', '#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_56, c_66, c_95])).
% 1.88/1.18  tff(c_99, plain, ('#skF_1'('#skF_3', '#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_98])).
% 1.88/1.18  tff(c_4, plain, (![A_1, B_7]: (~v3_tex_2('#skF_1'(A_1, B_7), A_1) | v4_tex_2(B_7, A_1) | ~m1_pre_topc(B_7, A_1) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.88/1.18  tff(c_103, plain, (~v3_tex_2('#skF_4', '#skF_3') | v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_4])).
% 1.88/1.18  tff(c_107, plain, (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_73, c_20, c_103])).
% 1.88/1.18  tff(c_108, plain, (v4_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_107])).
% 1.88/1.18  tff(c_112, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))!='#skF_4' | ~m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_108, c_18])).
% 1.88/1.18  tff(c_115, plain, (v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_73, c_66, c_112])).
% 1.88/1.18  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_115])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 16
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 0
% 1.88/1.18  #Demod        : 14
% 1.88/1.18  #Tautology    : 4
% 1.88/1.18  #SimpNegUnit  : 12
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.19  Preprocessing        : 0.30
% 1.88/1.19  Parsing              : 0.15
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.12
% 1.88/1.19  Inferencing          : 0.05
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
