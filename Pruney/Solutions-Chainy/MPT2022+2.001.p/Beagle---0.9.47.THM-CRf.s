%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 125 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 421 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_12,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_23,plain,(
    ! [A_26,B_27,C_28] :
      ( '#skF_1'(A_26,B_27,C_28) = C_28
      | ~ m1_subset_1(C_28,u1_struct_0(k9_yellow_6(A_26,B_27)))
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_29,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_26])).

tff(c_30,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_29])).

tff(c_35,plain,(
    ! [A_29,B_30,C_31] :
      ( v3_pre_topc('#skF_1'(A_29,B_30,C_31),A_29)
      | ~ m1_subset_1(C_31,u1_struct_0(k9_yellow_6(A_29,B_30)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_35])).

tff(c_40,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_30,c_37])).

tff(c_41,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_40])).

tff(c_42,plain,(
    ! [B_32,A_33,C_34] :
      ( r2_hidden(B_32,'#skF_1'(A_33,B_32,C_34))
      | ~ m1_subset_1(C_34,u1_struct_0(k9_yellow_6(A_33,B_32)))
      | ~ m1_subset_1(B_32,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,
    ( r2_hidden('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_42])).

tff(c_47,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_30,c_44])).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_47])).

tff(c_49,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1('#skF_1'(A_35,B_36,C_37),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(C_37,u1_struct_0(k9_yellow_6(A_35,B_36)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_35))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_52,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_49])).

tff(c_54,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_52])).

tff(c_55,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_54])).

tff(c_56,plain,(
    ! [B_38,A_39,C_40] :
      ( m1_connsp_2(B_38,A_39,C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ v3_pre_topc(B_38,A_39)
      | ~ m1_subset_1(C_40,u1_struct_0(A_39))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [B_38] :
      ( m1_connsp_2(B_38,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_38)
      | ~ v3_pre_topc(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_64,plain,(
    ! [B_38] :
      ( m1_connsp_2(B_38,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_38)
      | ~ v3_pre_topc(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_60])).

tff(c_66,plain,(
    ! [B_41] :
      ( m1_connsp_2(B_41,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_41)
      | ~ v3_pre_topc(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_64])).

tff(c_69,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_66])).

tff(c_76,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_48,c_69])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:40:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.13  
% 1.74/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.13  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.74/1.13  
% 1.74/1.13  %Foreground sorts:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Background operators:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Foreground operators:
% 1.74/1.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.74/1.13  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 1.74/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.74/1.13  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.74/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.13  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.74/1.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.74/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.13  
% 1.74/1.14  tff(f_82, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 1.74/1.14  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_yellow_6)).
% 1.74/1.14  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 1.74/1.14  tff(c_12, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_20, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_16, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_14, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.74/1.14  tff(c_23, plain, (![A_26, B_27, C_28]: ('#skF_1'(A_26, B_27, C_28)=C_28 | ~m1_subset_1(C_28, u1_struct_0(k9_yellow_6(A_26, B_27))) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.14  tff(c_26, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_23])).
% 1.74/1.14  tff(c_29, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_26])).
% 1.74/1.14  tff(c_30, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22, c_29])).
% 1.74/1.14  tff(c_35, plain, (![A_29, B_30, C_31]: (v3_pre_topc('#skF_1'(A_29, B_30, C_31), A_29) | ~m1_subset_1(C_31, u1_struct_0(k9_yellow_6(A_29, B_30))) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.14  tff(c_37, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_35])).
% 1.74/1.14  tff(c_40, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_30, c_37])).
% 1.74/1.14  tff(c_41, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_40])).
% 1.74/1.14  tff(c_42, plain, (![B_32, A_33, C_34]: (r2_hidden(B_32, '#skF_1'(A_33, B_32, C_34)) | ~m1_subset_1(C_34, u1_struct_0(k9_yellow_6(A_33, B_32))) | ~m1_subset_1(B_32, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.14  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_42])).
% 1.74/1.14  tff(c_47, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_30, c_44])).
% 1.74/1.14  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_22, c_47])).
% 1.74/1.14  tff(c_49, plain, (![A_35, B_36, C_37]: (m1_subset_1('#skF_1'(A_35, B_36, C_37), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(C_37, u1_struct_0(k9_yellow_6(A_35, B_36))) | ~m1_subset_1(B_36, u1_struct_0(A_35)) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.74/1.14  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_49])).
% 1.74/1.14  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_14, c_52])).
% 1.74/1.14  tff(c_55, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_54])).
% 1.74/1.14  tff(c_56, plain, (![B_38, A_39, C_40]: (m1_connsp_2(B_38, A_39, C_40) | ~r2_hidden(C_40, B_38) | ~v3_pre_topc(B_38, A_39) | ~m1_subset_1(C_40, u1_struct_0(A_39)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.74/1.14  tff(c_60, plain, (![B_38]: (m1_connsp_2(B_38, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_38) | ~v3_pre_topc(B_38, '#skF_2') | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.74/1.14  tff(c_64, plain, (![B_38]: (m1_connsp_2(B_38, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_38) | ~v3_pre_topc(B_38, '#skF_2') | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_60])).
% 1.74/1.14  tff(c_66, plain, (![B_41]: (m1_connsp_2(B_41, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_41) | ~v3_pre_topc(B_41, '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_64])).
% 1.74/1.14  tff(c_69, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_66])).
% 1.74/1.14  tff(c_76, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_48, c_69])).
% 1.74/1.14  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_76])).
% 1.74/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  Inference rules
% 1.74/1.14  ----------------------
% 1.74/1.14  #Ref     : 0
% 1.74/1.14  #Sup     : 10
% 1.74/1.14  #Fact    : 0
% 1.74/1.14  #Define  : 0
% 1.74/1.14  #Split   : 0
% 1.74/1.14  #Chain   : 0
% 1.74/1.14  #Close   : 0
% 1.74/1.14  
% 1.74/1.14  Ordering : KBO
% 1.74/1.14  
% 1.74/1.14  Simplification rules
% 1.74/1.14  ----------------------
% 1.74/1.14  #Subsume      : 0
% 1.74/1.14  #Demod        : 19
% 1.74/1.14  #Tautology    : 2
% 1.74/1.14  #SimpNegUnit  : 6
% 1.74/1.14  #BackRed      : 0
% 1.74/1.14  
% 1.74/1.14  #Partial instantiations: 0
% 1.74/1.14  #Strategies tried      : 1
% 1.74/1.14  
% 1.74/1.14  Timing (in seconds)
% 1.74/1.14  ----------------------
% 1.74/1.15  Preprocessing        : 0.27
% 1.74/1.15  Parsing              : 0.15
% 1.74/1.15  CNF conversion       : 0.02
% 1.74/1.15  Main loop            : 0.12
% 1.74/1.15  Inferencing          : 0.05
% 1.74/1.15  Reduction            : 0.03
% 1.74/1.15  Demodulation         : 0.03
% 1.74/1.15  BG Simplification    : 0.01
% 1.74/1.15  Subsumption          : 0.02
% 1.74/1.15  Abstraction          : 0.01
% 1.74/1.15  MUC search           : 0.00
% 1.74/1.15  Cooper               : 0.00
% 1.74/1.15  Total                : 0.42
% 1.74/1.15  Index Insertion      : 0.00
% 1.74/1.15  Index Deletion       : 0.00
% 1.74/1.15  Index Matching       : 0.00
% 1.74/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
