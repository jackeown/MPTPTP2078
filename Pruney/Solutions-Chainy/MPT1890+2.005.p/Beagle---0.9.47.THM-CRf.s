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
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 10.44s
% Output     : CNFRefutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 143 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  142 ( 549 expanded)
%              Number of equality atoms :   17 (  63 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_75,axiom,(
    ! [A] :
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

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14,plain,(
    ! [A_11,B_19] :
      ( m1_subset_1('#skF_1'(A_11,B_19),u1_struct_0(A_11))
      | v2_tex_2(B_19,A_11)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v3_tdlat_3(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | v2_tex_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v3_tdlat_3(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_127,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_140,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_127])).

tff(c_141,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_140])).

tff(c_18,plain,(
    ! [C_29] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_29))) = k6_domain_1(u1_struct_0('#skF_2'),C_29)
      | ~ r2_hidden(C_29,'#skF_3')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_33,C_34,B_35] :
      ( k9_subset_1(A_33,C_34,B_35) = k9_subset_1(A_33,B_35,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_36] : k9_subset_1(u1_struct_0('#skF_2'),B_36,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36) ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [B_36] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_4])).

tff(c_59,plain,(
    ! [B_36] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_49])).

tff(c_93,plain,(
    ! [A_42,B_43] :
      ( v4_pre_topc(k2_pre_topc(A_42,B_43),A_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    ! [B_36] :
      ( v4_pre_topc(k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36)),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_59,c_93])).

tff(c_111,plain,(
    ! [B_36] : v4_pre_topc(k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_99])).

tff(c_36,plain,(
    ! [B_35] : k9_subset_1(u1_struct_0('#skF_2'),B_35,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_35) ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_460,plain,(
    ! [A_74,B_75,D_76] :
      ( k9_subset_1(u1_struct_0(A_74),B_75,D_76) != k6_domain_1(u1_struct_0(A_74),'#skF_1'(A_74,B_75))
      | ~ v4_pre_topc(D_76,A_74)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_468,plain,(
    ! [B_35] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_35,'#skF_3') != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(B_35,'#skF_2')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_460])).

tff(c_479,plain,(
    ! [B_35] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_35,'#skF_3') != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(B_35,'#skF_2')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_468])).

tff(c_536,plain,(
    ! [B_81] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_81,'#skF_3') != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(B_81,'#skF_2')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_479])).

tff(c_555,plain,(
    ! [B_8] :
      ( k9_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_8),'#skF_3') != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',B_8),'#skF_2')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_536])).

tff(c_16153,plain,(
    ! [B_218] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',B_218)) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',B_218),'#skF_2')
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36,c_555])).

tff(c_16227,plain,(
    ! [B_36] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_36)),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_59,c_16153])).

tff(c_16374,plain,(
    ! [B_220] : k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_220))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_16227])).

tff(c_16387,plain,(
    ! [C_221] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_221))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(C_221,'#skF_3')
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16374])).

tff(c_16390,plain,(
    ! [C_29] :
      ( k6_domain_1(u1_struct_0('#skF_2'),C_29) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
      | ~ r2_hidden(C_29,'#skF_3')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2'))
      | ~ r2_hidden(C_29,'#skF_3')
      | ~ m1_subset_1(C_29,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16387])).

tff(c_16809,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16390])).

tff(c_16811,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_16809])).

tff(c_16815,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_16811])).

tff(c_16818,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_16815])).

tff(c_16820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16,c_16818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:55:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.44/4.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.44/4.03  
% 10.44/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.44/4.03  %$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.44/4.03  
% 10.44/4.03  %Foreground sorts:
% 10.44/4.03  
% 10.44/4.03  
% 10.44/4.03  %Background operators:
% 10.44/4.03  
% 10.44/4.03  
% 10.44/4.03  %Foreground operators:
% 10.44/4.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.44/4.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.44/4.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.44/4.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.44/4.03  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 10.44/4.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.44/4.03  tff('#skF_2', type, '#skF_2': $i).
% 10.44/4.03  tff('#skF_3', type, '#skF_3': $i).
% 10.44/4.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.44/4.03  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 10.44/4.03  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.44/4.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.44/4.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.44/4.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.44/4.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.44/4.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.44/4.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.44/4.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.44/4.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.44/4.03  
% 10.56/4.04  tff(f_97, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 10.56/4.04  tff(f_75, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 10.56/4.04  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 10.56/4.04  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 10.56/4.04  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.56/4.04  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.56/4.04  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_16, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_24, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_14, plain, (![A_11, B_19]: (m1_subset_1('#skF_1'(A_11, B_19), u1_struct_0(A_11)) | v2_tex_2(B_19, A_11) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v3_tdlat_3(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.56/4.04  tff(c_116, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | v2_tex_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v3_tdlat_3(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.56/4.04  tff(c_127, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_116])).
% 10.56/4.04  tff(c_140, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_127])).
% 10.56/4.04  tff(c_141, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_140])).
% 10.56/4.04  tff(c_18, plain, (![C_29]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_29)))=k6_domain_1(u1_struct_0('#skF_2'), C_29) | ~r2_hidden(C_29, '#skF_3') | ~m1_subset_1(C_29, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.56/4.04  tff(c_30, plain, (![A_33, C_34, B_35]: (k9_subset_1(A_33, C_34, B_35)=k9_subset_1(A_33, B_35, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.56/4.04  tff(c_37, plain, (![B_36]: (k9_subset_1(u1_struct_0('#skF_2'), B_36, '#skF_3')=k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36))), inference(resolution, [status(thm)], [c_20, c_30])).
% 10.56/4.04  tff(c_4, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.56/4.04  tff(c_49, plain, (![B_36]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_37, c_4])).
% 10.56/4.04  tff(c_59, plain, (![B_36]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36), k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_49])).
% 10.56/4.04  tff(c_93, plain, (![A_42, B_43]: (v4_pre_topc(k2_pre_topc(A_42, B_43), A_42) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.56/4.04  tff(c_99, plain, (![B_36]: (v4_pre_topc(k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36)), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_59, c_93])).
% 10.56/4.04  tff(c_111, plain, (![B_36]: (v4_pre_topc(k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_99])).
% 10.56/4.04  tff(c_36, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_2'), B_35, '#skF_3')=k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_35))), inference(resolution, [status(thm)], [c_20, c_30])).
% 10.56/4.04  tff(c_6, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.56/4.04  tff(c_460, plain, (![A_74, B_75, D_76]: (k9_subset_1(u1_struct_0(A_74), B_75, D_76)!=k6_domain_1(u1_struct_0(A_74), '#skF_1'(A_74, B_75)) | ~v4_pre_topc(D_76, A_74) | ~m1_subset_1(D_76, k1_zfmisc_1(u1_struct_0(A_74))) | v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.56/4.04  tff(c_468, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_2'), B_35, '#skF_3')!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(B_35, '#skF_2') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_460])).
% 10.56/4.04  tff(c_479, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_2'), B_35, '#skF_3')!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(B_35, '#skF_2') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_468])).
% 10.56/4.04  tff(c_536, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_2'), B_81, '#skF_3')!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(B_81, '#skF_2') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_479])).
% 10.56/4.04  tff(c_555, plain, (![B_8]: (k9_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_8), '#skF_3')!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', B_8), '#skF_2') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_536])).
% 10.56/4.04  tff(c_16153, plain, (![B_218]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', B_218))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', B_218), '#skF_2') | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36, c_555])).
% 10.56/4.04  tff(c_16227, plain, (![B_36]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36)))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~v4_pre_topc(k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_36)), '#skF_2'))), inference(resolution, [status(thm)], [c_59, c_16153])).
% 10.56/4.04  tff(c_16374, plain, (![B_220]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', B_220)))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_16227])).
% 10.56/4.04  tff(c_16387, plain, (![C_221]: (k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), C_221)))!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(C_221, '#skF_3') | ~m1_subset_1(C_221, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16374])).
% 10.56/4.04  tff(c_16390, plain, (![C_29]: (k6_domain_1(u1_struct_0('#skF_2'), C_29)!=k6_domain_1(u1_struct_0('#skF_2'), '#skF_1'('#skF_2', '#skF_3')) | ~r2_hidden(C_29, '#skF_3') | ~m1_subset_1(C_29, u1_struct_0('#skF_2')) | ~r2_hidden(C_29, '#skF_3') | ~m1_subset_1(C_29, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16387])).
% 10.56/4.04  tff(c_16809, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(reflexivity, [status(thm), theory('equality')], [c_16390])).
% 10.56/4.04  tff(c_16811, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_16809])).
% 10.56/4.04  tff(c_16815, plain, (v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_16811])).
% 10.56/4.04  tff(c_16818, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_16815])).
% 10.56/4.04  tff(c_16820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_16, c_16818])).
% 10.56/4.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/4.04  
% 10.56/4.04  Inference rules
% 10.56/4.04  ----------------------
% 10.56/4.04  #Ref     : 1
% 10.56/4.04  #Sup     : 3553
% 10.56/4.04  #Fact    : 0
% 10.56/4.04  #Define  : 0
% 10.56/4.04  #Split   : 3
% 10.56/4.04  #Chain   : 0
% 10.56/4.04  #Close   : 0
% 10.56/4.04  
% 10.56/4.04  Ordering : KBO
% 10.56/4.04  
% 10.56/4.04  Simplification rules
% 10.56/4.04  ----------------------
% 10.56/4.04  #Subsume      : 656
% 10.56/4.04  #Demod        : 2898
% 10.56/4.04  #Tautology    : 1296
% 10.56/4.04  #SimpNegUnit  : 125
% 10.56/4.04  #BackRed      : 0
% 10.56/4.04  
% 10.56/4.04  #Partial instantiations: 0
% 10.56/4.04  #Strategies tried      : 1
% 10.56/4.04  
% 10.56/4.04  Timing (in seconds)
% 10.56/4.04  ----------------------
% 10.56/4.05  Preprocessing        : 0.29
% 10.56/4.05  Parsing              : 0.17
% 10.56/4.05  CNF conversion       : 0.02
% 10.56/4.05  Main loop            : 2.98
% 10.56/4.05  Inferencing          : 0.80
% 10.56/4.05  Reduction            : 1.60
% 10.56/4.05  Demodulation         : 1.40
% 10.56/4.05  BG Simplification    : 0.09
% 10.56/4.05  Subsumption          : 0.37
% 10.56/4.05  Abstraction          : 0.17
% 10.56/4.05  MUC search           : 0.00
% 10.56/4.05  Cooper               : 0.00
% 10.56/4.05  Total                : 3.30
% 10.56/4.05  Index Insertion      : 0.00
% 10.56/4.05  Index Deletion       : 0.00
% 10.56/4.05  Index Matching       : 0.00
% 10.56/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
