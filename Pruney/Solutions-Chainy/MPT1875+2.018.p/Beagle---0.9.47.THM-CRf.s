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
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 146 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 342 expanded)
%              Number of equality atoms :    7 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_connsp_2(C,A,B)
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_20,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_56,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14,plain,(
    ! [A_15] :
      ( v2_tex_2(u1_struct_0(A_15),A_15)
      | ~ v1_tdlat_3(A_15)
      | ~ m1_subset_1(u1_struct_0(A_15),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_69,plain,(
    ! [A_32] :
      ( v2_tex_2(u1_struct_0(A_32),A_32)
      | ~ v1_tdlat_3(A_32)
      | ~ l1_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_14])).

tff(c_75,plain,
    ( v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_78,plain,
    ( v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_75])).

tff(c_79,plain,(
    v2_tex_2(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_78])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_80,plain,(
    ! [A_33,B_34] :
      ( m2_connsp_2(k2_struct_0(A_33),A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [B_34] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_80])).

tff(c_87,plain,(
    ! [B_34] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_82])).

tff(c_90,plain,(
    ! [B_35] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_87])).

tff(c_98,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_57,c_90])).

tff(c_107,plain,(
    ! [B_37,C_38,A_39] :
      ( r1_tarski(B_37,C_38)
      | ~ m2_connsp_2(C_38,A_39,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_113,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_107])).

tff(c_123,plain,
    ( r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_57,c_56,c_113])).

tff(c_124,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_123])).

tff(c_132,plain,(
    ! [C_41,A_42,B_43] :
      ( v2_tex_2(C_41,A_42)
      | ~ v2_tex_2(B_43,A_42)
      | ~ r1_tarski(C_41,B_43)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_142,plain,(
    ! [A_44] :
      ( v2_tex_2('#skF_2',A_44)
      | ~ v2_tex_2(k2_struct_0('#skF_1'),A_44)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_124,c_132])).

tff(c_145,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_142])).

tff(c_147,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_31,c_57,c_56,c_79,c_145])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:13:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  
% 1.75/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.16  %$ m2_connsp_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.75/1.16  
% 1.75/1.16  %Foreground sorts:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Background operators:
% 1.75/1.16  
% 1.75/1.16  
% 1.75/1.16  %Foreground operators:
% 1.75/1.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.75/1.16  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.75/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.16  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.75/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.75/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.75/1.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.75/1.16  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.75/1.16  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 1.75/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.16  
% 1.75/1.18  tff(f_107, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 1.75/1.18  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.75/1.18  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.75/1.18  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.75/1.18  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 1.75/1.18  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 1.75/1.18  tff(f_49, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 1.75/1.18  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_connsp_2)).
% 1.75/1.18  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 1.75/1.18  tff(c_20, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.18  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.18  tff(c_31, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.75/1.18  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.18  tff(c_47, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.18  tff(c_52, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_8, c_47])).
% 1.75/1.18  tff(c_56, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_52])).
% 1.75/1.18  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_57, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_22])).
% 1.75/1.18  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_26, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_14, plain, (![A_15]: (v2_tex_2(u1_struct_0(A_15), A_15) | ~v1_tdlat_3(A_15) | ~m1_subset_1(u1_struct_0(A_15), k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.75/1.18  tff(c_69, plain, (![A_32]: (v2_tex_2(u1_struct_0(A_32), A_32) | ~v1_tdlat_3(A_32) | ~l1_pre_topc(A_32) | v2_struct_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_14])).
% 1.75/1.18  tff(c_75, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_69])).
% 1.75/1.18  tff(c_78, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_75])).
% 1.75/1.18  tff(c_79, plain, (v2_tex_2(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_78])).
% 1.75/1.18  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 1.75/1.18  tff(c_80, plain, (![A_33, B_34]: (m2_connsp_2(k2_struct_0(A_33), A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.75/1.18  tff(c_82, plain, (![B_34]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_80])).
% 1.75/1.18  tff(c_87, plain, (![B_34]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_82])).
% 1.75/1.18  tff(c_90, plain, (![B_35]: (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_87])).
% 1.75/1.18  tff(c_98, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_57, c_90])).
% 1.75/1.18  tff(c_107, plain, (![B_37, C_38, A_39]: (r1_tarski(B_37, C_38) | ~m2_connsp_2(C_38, A_39, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.75/1.18  tff(c_113, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_98, c_107])).
% 1.75/1.18  tff(c_123, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_57, c_56, c_113])).
% 1.75/1.18  tff(c_124, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_123])).
% 1.75/1.18  tff(c_132, plain, (![C_41, A_42, B_43]: (v2_tex_2(C_41, A_42) | ~v2_tex_2(B_43, A_42) | ~r1_tarski(C_41, B_43) | ~m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.75/1.18  tff(c_142, plain, (![A_44]: (v2_tex_2('#skF_2', A_44) | ~v2_tex_2(k2_struct_0('#skF_1'), A_44) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_124, c_132])).
% 1.75/1.18  tff(c_145, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_142])).
% 1.75/1.18  tff(c_147, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_31, c_57, c_56, c_79, c_145])).
% 1.75/1.18  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_147])).
% 1.75/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  Inference rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Ref     : 0
% 1.75/1.18  #Sup     : 22
% 1.75/1.18  #Fact    : 0
% 1.75/1.18  #Define  : 0
% 1.75/1.18  #Split   : 0
% 1.75/1.18  #Chain   : 0
% 1.75/1.18  #Close   : 0
% 1.75/1.18  
% 1.75/1.18  Ordering : KBO
% 1.75/1.18  
% 1.75/1.18  Simplification rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Subsume      : 0
% 1.75/1.18  #Demod        : 30
% 1.75/1.18  #Tautology    : 9
% 1.75/1.18  #SimpNegUnit  : 8
% 1.75/1.18  #BackRed      : 1
% 1.75/1.18  
% 1.75/1.18  #Partial instantiations: 0
% 1.75/1.18  #Strategies tried      : 1
% 1.75/1.18  
% 1.75/1.18  Timing (in seconds)
% 1.75/1.18  ----------------------
% 2.03/1.18  Preprocessing        : 0.29
% 2.03/1.18  Parsing              : 0.16
% 2.03/1.18  CNF conversion       : 0.02
% 2.03/1.18  Main loop            : 0.14
% 2.03/1.18  Inferencing          : 0.05
% 2.03/1.18  Reduction            : 0.05
% 2.03/1.18  Demodulation         : 0.03
% 2.03/1.18  BG Simplification    : 0.01
% 2.03/1.18  Subsumption          : 0.02
% 2.03/1.18  Abstraction          : 0.01
% 2.03/1.18  MUC search           : 0.00
% 2.03/1.18  Cooper               : 0.00
% 2.03/1.18  Total                : 0.46
% 2.03/1.18  Index Insertion      : 0.00
% 2.03/1.18  Index Deletion       : 0.00
% 2.03/1.18  Index Matching       : 0.00
% 2.03/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
