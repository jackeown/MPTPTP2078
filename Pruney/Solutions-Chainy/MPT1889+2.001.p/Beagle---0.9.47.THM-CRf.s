%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 183 expanded)
%              Number of leaves         :   24 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 932 expanded)
%              Number of equality atoms :    8 (  77 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    ! [A_5,B_13] :
      ( m1_subset_1('#skF_2'(A_5,B_13),u1_struct_0(A_5))
      | v2_tex_2(B_13,A_5)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_71,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),B_42)
      | v2_tex_2(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_71])).

tff(c_85,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_77])).

tff(c_86,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_16,c_85])).

tff(c_32,plain,(
    ! [C_29] :
      ( m1_subset_1('#skF_5'(C_29),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [C_29] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'(C_29)) = k6_domain_1(u1_struct_0('#skF_3'),C_29)
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    ! [A_47,B_48,D_49] :
      ( k9_subset_1(u1_struct_0(A_47),B_48,D_49) != k6_domain_1(u1_struct_0(A_47),'#skF_2'(A_47,B_48))
      | ~ v3_pre_topc(D_49,A_47)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | v2_tex_2(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [C_29] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_29) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_29),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_90])).

tff(c_94,plain,(
    ! [C_29] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_29) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_29),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_18,c_92])).

tff(c_96,plain,(
    ! [C_50] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_50) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_50),'#skF_3')
      | ~ m1_subset_1('#skF_5'(C_50),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_50,'#skF_4')
      | ~ m1_subset_1(C_50,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_16,c_94])).

tff(c_100,plain,(
    ! [C_29] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_29) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_96])).

tff(c_103,plain,
    ( ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_100])).

tff(c_105,plain,
    ( ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_103])).

tff(c_107,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_110,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_107])).

tff(c_113,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_18,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_16,c_113])).

tff(c_117,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_30,plain,(
    ! [C_29] :
      ( v4_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ! [B_36,A_37] :
      ( v3_pre_topc(B_36,A_37)
      | ~ v4_pre_topc(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ v3_tdlat_3(A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [C_29] :
      ( v3_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ v4_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_56,plain,(
    ! [C_38] :
      ( v3_pre_topc('#skF_5'(C_38),'#skF_3')
      | ~ v4_pre_topc('#skF_5'(C_38),'#skF_3')
      | ~ r2_hidden(C_38,'#skF_4')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_22,c_44])).

tff(c_60,plain,(
    ! [C_29] :
      ( v3_pre_topc('#skF_5'(C_29),'#skF_3')
      | ~ r2_hidden(C_29,'#skF_4')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_116,plain,(
    ~ v3_pre_topc('#skF_5'('#skF_2'('#skF_3','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_120,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_123,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_120])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.31  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.00/1.31  
% 2.00/1.31  %Foreground sorts:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Background operators:
% 2.00/1.31  
% 2.00/1.31  
% 2.00/1.31  %Foreground operators:
% 2.00/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.00/1.31  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.00/1.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.00/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.00/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.00/1.31  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.00/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.31  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.00/1.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.00/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.00/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.31  
% 2.00/1.32  tff(f_93, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 2.00/1.32  tff(f_64, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 2.00/1.32  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.00/1.32  tff(c_26, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_16, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_24, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_20, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_14, plain, (![A_5, B_13]: (m1_subset_1('#skF_2'(A_5, B_13), u1_struct_0(A_5)) | v2_tex_2(B_13, A_5) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.32  tff(c_71, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), B_42) | v2_tex_2(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.32  tff(c_77, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_71])).
% 2.00/1.32  tff(c_85, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_77])).
% 2.00/1.32  tff(c_86, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_26, c_16, c_85])).
% 2.00/1.32  tff(c_32, plain, (![C_29]: (m1_subset_1('#skF_5'(C_29), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_28, plain, (![C_29]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'(C_29))=k6_domain_1(u1_struct_0('#skF_3'), C_29) | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_90, plain, (![A_47, B_48, D_49]: (k9_subset_1(u1_struct_0(A_47), B_48, D_49)!=k6_domain_1(u1_struct_0(A_47), '#skF_2'(A_47, B_48)) | ~v3_pre_topc(D_49, A_47) | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0(A_47))) | v2_tex_2(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.32  tff(c_92, plain, (![C_29]: (k6_domain_1(u1_struct_0('#skF_3'), C_29)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc('#skF_5'(C_29), '#skF_3') | ~m1_subset_1('#skF_5'(C_29), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28, c_90])).
% 2.00/1.32  tff(c_94, plain, (![C_29]: (k6_domain_1(u1_struct_0('#skF_3'), C_29)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc('#skF_5'(C_29), '#skF_3') | ~m1_subset_1('#skF_5'(C_29), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_18, c_92])).
% 2.00/1.32  tff(c_96, plain, (![C_50]: (k6_domain_1(u1_struct_0('#skF_3'), C_50)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc('#skF_5'(C_50), '#skF_3') | ~m1_subset_1('#skF_5'(C_50), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_50, '#skF_4') | ~m1_subset_1(C_50, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_26, c_16, c_94])).
% 2.00/1.32  tff(c_100, plain, (![C_29]: (k6_domain_1(u1_struct_0('#skF_3'), C_29)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc('#skF_5'(C_29), '#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_96])).
% 2.00/1.32  tff(c_103, plain, (~v3_pre_topc('#skF_5'('#skF_2'('#skF_3', '#skF_4')), '#skF_3') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_100])).
% 2.00/1.32  tff(c_105, plain, (~v3_pre_topc('#skF_5'('#skF_2'('#skF_3', '#skF_4')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_103])).
% 2.00/1.32  tff(c_107, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_105])).
% 2.00/1.32  tff(c_110, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_107])).
% 2.00/1.32  tff(c_113, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_18, c_110])).
% 2.00/1.32  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_16, c_113])).
% 2.00/1.32  tff(c_117, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_105])).
% 2.00/1.32  tff(c_30, plain, (![C_29]: (v4_pre_topc('#skF_5'(C_29), '#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_22, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.00/1.32  tff(c_38, plain, (![B_36, A_37]: (v3_pre_topc(B_36, A_37) | ~v4_pre_topc(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~v3_tdlat_3(A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.00/1.32  tff(c_44, plain, (![C_29]: (v3_pre_topc('#skF_5'(C_29), '#skF_3') | ~v4_pre_topc('#skF_5'(C_29), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.00/1.32  tff(c_56, plain, (![C_38]: (v3_pre_topc('#skF_5'(C_38), '#skF_3') | ~v4_pre_topc('#skF_5'(C_38), '#skF_3') | ~r2_hidden(C_38, '#skF_4') | ~m1_subset_1(C_38, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_22, c_44])).
% 2.00/1.32  tff(c_60, plain, (![C_29]: (v3_pre_topc('#skF_5'(C_29), '#skF_3') | ~r2_hidden(C_29, '#skF_4') | ~m1_subset_1(C_29, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_30, c_56])).
% 2.00/1.32  tff(c_116, plain, (~v3_pre_topc('#skF_5'('#skF_2'('#skF_3', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_105])).
% 2.00/1.32  tff(c_120, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_116])).
% 2.00/1.32  tff(c_123, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_120])).
% 2.00/1.32  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_123])).
% 2.00/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.32  
% 2.00/1.32  Inference rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Ref     : 1
% 2.00/1.32  #Sup     : 13
% 2.00/1.32  #Fact    : 0
% 2.00/1.32  #Define  : 0
% 2.00/1.32  #Split   : 2
% 2.00/1.32  #Chain   : 0
% 2.00/1.32  #Close   : 0
% 2.00/1.32  
% 2.00/1.32  Ordering : KBO
% 2.00/1.32  
% 2.00/1.32  Simplification rules
% 2.00/1.32  ----------------------
% 2.00/1.32  #Subsume      : 2
% 2.00/1.32  #Demod        : 19
% 2.00/1.32  #Tautology    : 3
% 2.00/1.32  #SimpNegUnit  : 4
% 2.00/1.32  #BackRed      : 0
% 2.00/1.32  
% 2.00/1.32  #Partial instantiations: 0
% 2.00/1.32  #Strategies tried      : 1
% 2.00/1.32  
% 2.00/1.32  Timing (in seconds)
% 2.00/1.32  ----------------------
% 2.00/1.32  Preprocessing        : 0.31
% 2.00/1.32  Parsing              : 0.18
% 2.00/1.32  CNF conversion       : 0.02
% 2.00/1.32  Main loop            : 0.16
% 2.00/1.32  Inferencing          : 0.07
% 2.00/1.32  Reduction            : 0.04
% 2.00/1.32  Demodulation         : 0.03
% 2.00/1.32  BG Simplification    : 0.01
% 2.00/1.32  Subsumption          : 0.02
% 2.00/1.32  Abstraction          : 0.01
% 2.00/1.32  MUC search           : 0.00
% 2.00/1.32  Cooper               : 0.00
% 2.00/1.32  Total                : 0.51
% 2.00/1.32  Index Insertion      : 0.00
% 2.00/1.32  Index Deletion       : 0.00
% 2.00/1.32  Index Matching       : 0.00
% 2.00/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
