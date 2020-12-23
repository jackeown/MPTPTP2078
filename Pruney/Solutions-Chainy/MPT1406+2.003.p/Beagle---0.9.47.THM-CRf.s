%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 192 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 502 expanded)
%              Number of equality atoms :    1 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m2_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_293,plain,(
    ! [C_93,A_94,B_95] :
      ( m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m2_connsp_2(C_93,A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_295,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_293])).

tff(c_298,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_295])).

tff(c_22,plain,(
    ! [A_13,B_15] :
      ( r1_tarski(k1_tops_1(A_13,B_15),B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_300,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_22])).

tff(c_308,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_300])).

tff(c_70,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tops_1(A_48,B_49),B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_79,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_75])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [A_41,C_42,B_43] :
      ( m1_subset_1(A_41,C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [A_45,B_46,A_47] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_18,c_58])).

tff(c_80,plain,(
    ! [C_50,B_51,A_52] :
      ( m1_subset_1(C_50,B_51)
      | ~ r1_tarski(k1_zfmisc_1(A_52),B_51)
      | ~ r1_tarski(C_50,A_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_84,plain,(
    ! [C_53,B_54,A_55] :
      ( m1_subset_1(C_53,k1_zfmisc_1(B_54))
      | ~ r1_tarski(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_95,plain,(
    ! [B_57] :
      ( m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(B_57))
      | ~ r1_tarski('#skF_4',B_57) ) ),
    inference(resolution,[status(thm)],[c_79,c_84])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [B_58] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_58)
      | ~ r1_tarski('#skF_4',B_58) ) ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_83,plain,(
    ! [C_50,B_7,A_6] :
      ( m1_subset_1(C_50,k1_zfmisc_1(B_7))
      | ~ r1_tarski(C_50,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_110,plain,(
    ! [B_7,B_58] :
      ( m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1(B_7))
      | ~ r1_tarski(B_58,B_7)
      | ~ r1_tarski('#skF_4',B_58) ) ),
    inference(resolution,[status(thm)],[c_107,c_83])).

tff(c_326,plain,
    ( m1_subset_1(k1_tops_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_308,c_110])).

tff(c_474,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_384,plain,(
    ! [B_102,A_103,C_104] :
      ( r1_tarski(B_102,k1_tops_1(A_103,C_104))
      | ~ m2_connsp_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_389,plain,(
    ! [B_102] :
      ( r1_tarski(B_102,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_298,c_384])).

tff(c_818,plain,(
    ! [B_144] :
      ( r1_tarski(B_144,k1_tops_1('#skF_3','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_3',B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_389])).

tff(c_836,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m2_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_818])).

tff(c_849,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_836])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_849])).

tff(c_853,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_941,plain,(
    ! [B_147] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_147))
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_147) ) ),
    inference(resolution,[status(thm)],[c_853,c_83])).

tff(c_958,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_308,c_941])).

tff(c_966,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_958,c_16])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:28:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.56  
% 3.61/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.56  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.61/1.56  
% 3.61/1.56  %Foreground sorts:
% 3.61/1.56  
% 3.61/1.56  
% 3.61/1.56  %Background operators:
% 3.61/1.56  
% 3.61/1.56  
% 3.61/1.56  %Foreground operators:
% 3.61/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.61/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.61/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.56  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.61/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.56  
% 3.75/1.57  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 3.75/1.57  tff(f_78, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 3.75/1.57  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.75/1.57  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.75/1.57  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.75/1.57  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.57  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.75/1.57  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.75/1.57  tff(c_30, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.57  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.57  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.57  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.57  tff(c_32, plain, (m2_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.75/1.57  tff(c_293, plain, (![C_93, A_94, B_95]: (m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~m2_connsp_2(C_93, A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.75/1.57  tff(c_295, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_293])).
% 3.75/1.57  tff(c_298, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_295])).
% 3.75/1.57  tff(c_22, plain, (![A_13, B_15]: (r1_tarski(k1_tops_1(A_13, B_15), B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.57  tff(c_300, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_298, c_22])).
% 3.75/1.57  tff(c_308, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_300])).
% 3.75/1.57  tff(c_70, plain, (![A_48, B_49]: (r1_tarski(k1_tops_1(A_48, B_49), B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.57  tff(c_75, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_70])).
% 3.75/1.57  tff(c_79, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_75])).
% 3.75/1.57  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.57  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.57  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.75/1.57  tff(c_58, plain, (![A_41, C_42, B_43]: (m1_subset_1(A_41, C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.57  tff(c_66, plain, (![A_45, B_46, A_47]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, A_47) | ~r1_tarski(A_47, B_46))), inference(resolution, [status(thm)], [c_18, c_58])).
% 3.75/1.57  tff(c_80, plain, (![C_50, B_51, A_52]: (m1_subset_1(C_50, B_51) | ~r1_tarski(k1_zfmisc_1(A_52), B_51) | ~r1_tarski(C_50, A_52))), inference(resolution, [status(thm)], [c_4, c_66])).
% 3.75/1.57  tff(c_84, plain, (![C_53, B_54, A_55]: (m1_subset_1(C_53, k1_zfmisc_1(B_54)) | ~r1_tarski(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_14, c_80])).
% 3.75/1.57  tff(c_95, plain, (![B_57]: (m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(B_57)) | ~r1_tarski('#skF_4', B_57))), inference(resolution, [status(thm)], [c_79, c_84])).
% 3.75/1.57  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.75/1.57  tff(c_107, plain, (![B_58]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_58) | ~r1_tarski('#skF_4', B_58))), inference(resolution, [status(thm)], [c_95, c_16])).
% 3.75/1.57  tff(c_83, plain, (![C_50, B_7, A_6]: (m1_subset_1(C_50, k1_zfmisc_1(B_7)) | ~r1_tarski(C_50, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_14, c_80])).
% 3.75/1.57  tff(c_110, plain, (![B_7, B_58]: (m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1(B_7)) | ~r1_tarski(B_58, B_7) | ~r1_tarski('#skF_4', B_58))), inference(resolution, [status(thm)], [c_107, c_83])).
% 3.75/1.57  tff(c_326, plain, (m1_subset_1(k1_tops_1('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_308, c_110])).
% 3.75/1.57  tff(c_474, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_326])).
% 3.75/1.57  tff(c_384, plain, (![B_102, A_103, C_104]: (r1_tarski(B_102, k1_tops_1(A_103, C_104)) | ~m2_connsp_2(C_104, A_103, B_102) | ~m1_subset_1(C_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.75/1.57  tff(c_389, plain, (![B_102]: (r1_tarski(B_102, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_298, c_384])).
% 3.75/1.57  tff(c_818, plain, (![B_144]: (r1_tarski(B_144, k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_389])).
% 3.75/1.57  tff(c_836, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_818])).
% 3.75/1.57  tff(c_849, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_836])).
% 3.75/1.57  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_849])).
% 3.75/1.57  tff(c_853, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_326])).
% 3.75/1.57  tff(c_941, plain, (![B_147]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_147)) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_147))), inference(resolution, [status(thm)], [c_853, c_83])).
% 3.75/1.57  tff(c_958, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_308, c_941])).
% 3.75/1.57  tff(c_966, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_958, c_16])).
% 3.75/1.57  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_966])).
% 3.75/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.57  
% 3.75/1.57  Inference rules
% 3.75/1.57  ----------------------
% 3.75/1.57  #Ref     : 0
% 3.75/1.57  #Sup     : 231
% 3.75/1.57  #Fact    : 0
% 3.75/1.57  #Define  : 0
% 3.75/1.57  #Split   : 11
% 3.75/1.57  #Chain   : 0
% 3.75/1.57  #Close   : 0
% 3.75/1.57  
% 3.75/1.57  Ordering : KBO
% 3.75/1.57  
% 3.75/1.57  Simplification rules
% 3.75/1.57  ----------------------
% 3.75/1.57  #Subsume      : 25
% 3.75/1.57  #Demod        : 23
% 3.75/1.57  #Tautology    : 5
% 3.75/1.57  #SimpNegUnit  : 4
% 3.75/1.57  #BackRed      : 0
% 3.75/1.57  
% 3.75/1.57  #Partial instantiations: 0
% 3.75/1.57  #Strategies tried      : 1
% 3.75/1.57  
% 3.75/1.57  Timing (in seconds)
% 3.75/1.57  ----------------------
% 3.75/1.58  Preprocessing        : 0.30
% 3.75/1.58  Parsing              : 0.16
% 3.75/1.58  CNF conversion       : 0.02
% 3.75/1.58  Main loop            : 0.53
% 3.75/1.58  Inferencing          : 0.17
% 3.75/1.58  Reduction            : 0.13
% 3.75/1.58  Demodulation         : 0.09
% 3.75/1.58  BG Simplification    : 0.02
% 3.75/1.58  Subsumption          : 0.15
% 3.75/1.58  Abstraction          : 0.02
% 3.75/1.58  MUC search           : 0.00
% 3.75/1.58  Cooper               : 0.00
% 3.75/1.58  Total                : 0.86
% 3.75/1.58  Index Insertion      : 0.00
% 3.75/1.58  Index Deletion       : 0.00
% 3.75/1.58  Index Matching       : 0.00
% 3.75/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
