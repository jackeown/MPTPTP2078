%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:07 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 159 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 451 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_tex_2(k1_tex_2(A,B),A)
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tex_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_50,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_69,plain,(
    ! [A_41,B_42] :
      ( m1_pre_topc(k1_tex_2(A_41,B_42),A_41)
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_74,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_71])).

tff(c_75,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_74])).

tff(c_32,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( m1_subset_1(u1_struct_0(B_4),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [B_53,A_54] :
      ( v1_subset_1(u1_struct_0(B_53),u1_struct_0(A_54))
      | ~ m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ v1_tex_2(B_53,A_54)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [B_4,A_2] :
      ( v1_subset_1(u1_struct_0(B_4),u1_struct_0(A_2))
      | ~ v1_tex_2(B_4,A_2)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_61,plain,(
    ! [A_39,B_40] :
      ( ~ v2_struct_0(k1_tex_2(A_39,B_40))
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l1_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_61])).

tff(c_67,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_64])).

tff(c_68,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_67])).

tff(c_52,plain,(
    ! [A_36,B_37] :
      ( v1_pre_topc(k1_tex_2(A_36,B_37))
      | ~ m1_subset_1(B_37,u1_struct_0(A_36))
      | ~ l1_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_58,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_55])).

tff(c_59,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_58])).

tff(c_121,plain,(
    ! [A_66,B_67] :
      ( k6_domain_1(u1_struct_0(A_66),B_67) = u1_struct_0(k1_tex_2(A_66,B_67))
      | ~ m1_pre_topc(k1_tex_2(A_66,B_67),A_66)
      | ~ v1_pre_topc(k1_tex_2(A_66,B_67))
      | v2_struct_0(k1_tex_2(A_66,B_67))
      | ~ m1_subset_1(B_67,u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_121])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_59,c_123])).

tff(c_127,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_68,c_126])).

tff(c_28,plain,(
    ! [A_26,B_28] :
      ( ~ v7_struct_0(A_26)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_26),B_28),u1_struct_0(A_26))
      | ~ m1_subset_1(B_28,u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_133,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_140,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_133])).

tff(c_141,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_140])).

tff(c_143,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_146,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_146])).

tff(c_151,plain,(
    ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_155,plain,
    ( ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_151])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_75,c_32,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.33  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.27/1.33  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.27/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.27/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.27/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.27/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.33  
% 2.27/1.34  tff(f_118, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_tex_2(k1_tex_2(A, B), A) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tex_2)).
% 2.27/1.34  tff(f_91, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.27/1.34  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.27/1.34  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.27/1.34  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.27/1.34  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.27/1.34  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.27/1.34  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.34  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.34  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.34  tff(c_69, plain, (![A_41, B_42]: (m1_pre_topc(k1_tex_2(A_41, B_42), A_41) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.27/1.34  tff(c_71, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_69])).
% 2.27/1.34  tff(c_74, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_71])).
% 2.27/1.34  tff(c_75, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_74])).
% 2.27/1.34  tff(c_32, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.34  tff(c_4, plain, (![B_4, A_2]: (m1_subset_1(u1_struct_0(B_4), k1_zfmisc_1(u1_struct_0(A_2))) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.34  tff(c_91, plain, (![B_53, A_54]: (v1_subset_1(u1_struct_0(B_53), u1_struct_0(A_54)) | ~m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_54))) | ~v1_tex_2(B_53, A_54) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.27/1.34  tff(c_95, plain, (![B_4, A_2]: (v1_subset_1(u1_struct_0(B_4), u1_struct_0(A_2)) | ~v1_tex_2(B_4, A_2) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.27/1.34  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.34  tff(c_30, plain, (v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.27/1.34  tff(c_61, plain, (![A_39, B_40]: (~v2_struct_0(k1_tex_2(A_39, B_40)) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l1_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.27/1.34  tff(c_64, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_61])).
% 2.27/1.34  tff(c_67, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_64])).
% 2.27/1.34  tff(c_68, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_67])).
% 2.27/1.34  tff(c_52, plain, (![A_36, B_37]: (v1_pre_topc(k1_tex_2(A_36, B_37)) | ~m1_subset_1(B_37, u1_struct_0(A_36)) | ~l1_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.27/1.34  tff(c_55, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.27/1.34  tff(c_58, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_55])).
% 2.27/1.34  tff(c_59, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_58])).
% 2.27/1.34  tff(c_121, plain, (![A_66, B_67]: (k6_domain_1(u1_struct_0(A_66), B_67)=u1_struct_0(k1_tex_2(A_66, B_67)) | ~m1_pre_topc(k1_tex_2(A_66, B_67), A_66) | ~v1_pre_topc(k1_tex_2(A_66, B_67)) | v2_struct_0(k1_tex_2(A_66, B_67)) | ~m1_subset_1(B_67, u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.34  tff(c_123, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_75, c_121])).
% 2.27/1.34  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_59, c_123])).
% 2.27/1.34  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_68, c_126])).
% 2.27/1.34  tff(c_28, plain, (![A_26, B_28]: (~v7_struct_0(A_26) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_26), B_28), u1_struct_0(A_26)) | ~m1_subset_1(B_28, u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.34  tff(c_133, plain, (~v7_struct_0('#skF_2') | ~v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_28])).
% 2.27/1.34  tff(c_140, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_133])).
% 2.27/1.34  tff(c_141, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_140])).
% 2.27/1.34  tff(c_143, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_141])).
% 2.27/1.34  tff(c_146, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_143])).
% 2.27/1.34  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_146])).
% 2.27/1.34  tff(c_151, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_141])).
% 2.27/1.34  tff(c_155, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_95, c_151])).
% 2.27/1.34  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_75, c_32, c_155])).
% 2.27/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  Inference rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Ref     : 0
% 2.27/1.34  #Sup     : 20
% 2.27/1.34  #Fact    : 0
% 2.27/1.34  #Define  : 0
% 2.27/1.34  #Split   : 1
% 2.27/1.34  #Chain   : 0
% 2.27/1.34  #Close   : 0
% 2.27/1.34  
% 2.27/1.34  Ordering : KBO
% 2.27/1.34  
% 2.27/1.34  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 3
% 2.27/1.35  #Demod        : 14
% 2.27/1.35  #Tautology    : 3
% 2.27/1.35  #SimpNegUnit  : 6
% 2.27/1.35  #BackRed      : 0
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.35  Preprocessing        : 0.32
% 2.27/1.35  Parsing              : 0.16
% 2.27/1.35  CNF conversion       : 0.02
% 2.27/1.35  Main loop            : 0.25
% 2.27/1.35  Inferencing          : 0.10
% 2.27/1.35  Reduction            : 0.06
% 2.27/1.35  Demodulation         : 0.05
% 2.27/1.35  BG Simplification    : 0.02
% 2.27/1.35  Subsumption          : 0.04
% 2.27/1.35  Abstraction          : 0.01
% 2.27/1.35  MUC search           : 0.00
% 2.27/1.35  Cooper               : 0.00
% 2.27/1.35  Total                : 0.60
% 2.27/1.35  Index Insertion      : 0.00
% 2.27/1.35  Index Deletion       : 0.00
% 2.27/1.35  Index Matching       : 0.00
% 2.27/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
