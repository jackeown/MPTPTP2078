%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 164 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  141 ( 518 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [A_27] :
      ( v1_xboole_0(A_27)
      | r2_hidden('#skF_1'(A_27),A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_1'(A_27),A_27)
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_34,c_6])).

tff(c_28,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_11),B_13),A_11)
      | ~ m1_subset_1(B_13,u1_struct_0(A_11))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k6_domain_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [A_38,B_39] :
      ( v3_tex_2('#skF_2'(A_38,B_39),A_38)
      | ~ v2_tex_2(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v3_tdlat_3(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_148,plain,(
    ! [A_50,B_51] :
      ( v3_tex_2('#skF_2'(A_50,k6_domain_1(u1_struct_0(A_50),B_51)),A_50)
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(A_50),B_51),A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v3_tdlat_3(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50)
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | v1_xboole_0(u1_struct_0(A_50)) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1('#skF_2'(A_40,B_41),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v2_tex_2(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v3_tdlat_3(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    ! [B_21] :
      ( ~ v3_tex_2(B_21,'#skF_3')
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87,plain,(
    ! [B_41] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_41),'#skF_3')
      | ~ v2_tex_2(B_41,'#skF_3')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_79,c_22])).

tff(c_92,plain,(
    ! [B_41] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_41),'#skF_3')
      | ~ v2_tex_2(B_41,'#skF_3')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_87])).

tff(c_94,plain,(
    ! [B_42] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_42),'#skF_3')
      | ~ v2_tex_2(B_42,'#skF_3')
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_92])).

tff(c_111,plain,(
    ! [B_10] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_10),'#skF_3')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_94])).

tff(c_115,plain,(
    ! [B_10] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_10)),'#skF_3')
      | ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_10),'#skF_3')
      | ~ m1_subset_1(B_10,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_152,plain,(
    ! [B_51] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_51),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_148,c_115])).

tff(c_155,plain,(
    ! [B_51] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_51),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_152])).

tff(c_156,plain,(
    ! [B_51] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_51),'#skF_3')
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_155])).

tff(c_158,plain,(
    ! [B_52] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),B_52),'#skF_3')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_162,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_165,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_162])).

tff(c_167,plain,(
    ! [B_53] : ~ m1_subset_1(B_53,u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_165])).

tff(c_172,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_41,c_167])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_179,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_176])).

tff(c_182,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_182])).

tff(c_187,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_190,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_10])).

tff(c_193,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_190])).

tff(c_196,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_196])).

tff(c_201,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_204,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_201,c_10])).

tff(c_207,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_204])).

tff(c_210,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.22  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2
% 1.89/1.22  
% 1.89/1.22  %Foreground sorts:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Background operators:
% 1.89/1.22  
% 1.89/1.22  
% 1.89/1.22  %Foreground operators:
% 1.89/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.89/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.89/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.22  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 1.89/1.22  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.89/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.89/1.22  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.89/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.22  
% 2.18/1.23  tff(f_104, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.18/1.23  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.18/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.18/1.23  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.18/1.23  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.18/1.23  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.18/1.23  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.18/1.23  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.18/1.23  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.18/1.23  tff(c_8, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.23  tff(c_30, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.18/1.23  tff(c_34, plain, (![A_27]: (v1_xboole_0(A_27) | r2_hidden('#skF_1'(A_27), A_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.23  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.23  tff(c_41, plain, (![A_27]: (m1_subset_1('#skF_1'(A_27), A_27) | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_34, c_6])).
% 2.18/1.23  tff(c_28, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.18/1.23  tff(c_14, plain, (![A_11, B_13]: (v2_tex_2(k6_domain_1(u1_struct_0(A_11), B_13), A_11) | ~m1_subset_1(B_13, u1_struct_0(A_11)) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.18/1.23  tff(c_26, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.18/1.23  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k6_domain_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.23  tff(c_70, plain, (![A_38, B_39]: (v3_tex_2('#skF_2'(A_38, B_39), A_38) | ~v2_tex_2(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v3_tdlat_3(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.18/1.23  tff(c_148, plain, (![A_50, B_51]: (v3_tex_2('#skF_2'(A_50, k6_domain_1(u1_struct_0(A_50), B_51)), A_50) | ~v2_tex_2(k6_domain_1(u1_struct_0(A_50), B_51), A_50) | ~l1_pre_topc(A_50) | ~v3_tdlat_3(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | v1_xboole_0(u1_struct_0(A_50)))), inference(resolution, [status(thm)], [c_12, c_70])).
% 2.18/1.23  tff(c_79, plain, (![A_40, B_41]: (m1_subset_1('#skF_2'(A_40, B_41), k1_zfmisc_1(u1_struct_0(A_40))) | ~v2_tex_2(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v3_tdlat_3(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.18/1.23  tff(c_22, plain, (![B_21]: (~v3_tex_2(B_21, '#skF_3') | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.18/1.23  tff(c_87, plain, (![B_41]: (~v3_tex_2('#skF_2'('#skF_3', B_41), '#skF_3') | ~v2_tex_2(B_41, '#skF_3') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_22])).
% 2.18/1.23  tff(c_92, plain, (![B_41]: (~v3_tex_2('#skF_2'('#skF_3', B_41), '#skF_3') | ~v2_tex_2(B_41, '#skF_3') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_87])).
% 2.18/1.23  tff(c_94, plain, (![B_42]: (~v3_tex_2('#skF_2'('#skF_3', B_42), '#skF_3') | ~v2_tex_2(B_42, '#skF_3') | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_92])).
% 2.18/1.23  tff(c_111, plain, (![B_10]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_10), '#skF_3') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_94])).
% 2.18/1.23  tff(c_115, plain, (![B_10]: (~v3_tex_2('#skF_2'('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_10)), '#skF_3') | ~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_10), '#skF_3') | ~m1_subset_1(B_10, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_111])).
% 2.18/1.23  tff(c_152, plain, (![B_51]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_51), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_148, c_115])).
% 2.18/1.23  tff(c_155, plain, (![B_51]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_51), '#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_152])).
% 2.18/1.23  tff(c_156, plain, (![B_51]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_51), '#skF_3') | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_155])).
% 2.18/1.23  tff(c_158, plain, (![B_52]: (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'), B_52), '#skF_3') | ~m1_subset_1(B_52, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_156])).
% 2.18/1.23  tff(c_162, plain, (![B_13]: (~m1_subset_1(B_13, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_158])).
% 2.18/1.23  tff(c_165, plain, (![B_13]: (~m1_subset_1(B_13, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_162])).
% 2.18/1.23  tff(c_167, plain, (![B_53]: (~m1_subset_1(B_53, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_30, c_165])).
% 2.18/1.23  tff(c_172, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_41, c_167])).
% 2.18/1.23  tff(c_10, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.23  tff(c_176, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_172, c_10])).
% 2.18/1.23  tff(c_179, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_176])).
% 2.18/1.23  tff(c_182, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_179])).
% 2.18/1.23  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_182])).
% 2.18/1.23  tff(c_187, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_156])).
% 2.18/1.23  tff(c_190, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_187, c_10])).
% 2.18/1.23  tff(c_193, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_190])).
% 2.18/1.23  tff(c_196, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_193])).
% 2.18/1.23  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_196])).
% 2.18/1.23  tff(c_201, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_111])).
% 2.18/1.23  tff(c_204, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_201, c_10])).
% 2.18/1.23  tff(c_207, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_204])).
% 2.18/1.23  tff(c_210, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.18/1.23  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_210])).
% 2.18/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.23  
% 2.18/1.23  Inference rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Ref     : 0
% 2.18/1.23  #Sup     : 27
% 2.18/1.23  #Fact    : 0
% 2.18/1.23  #Define  : 0
% 2.18/1.23  #Split   : 6
% 2.18/1.23  #Chain   : 0
% 2.18/1.23  #Close   : 0
% 2.18/1.23  
% 2.18/1.23  Ordering : KBO
% 2.18/1.23  
% 2.18/1.23  Simplification rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Subsume      : 7
% 2.18/1.23  #Demod        : 20
% 2.18/1.23  #Tautology    : 1
% 2.18/1.23  #SimpNegUnit  : 9
% 2.18/1.23  #BackRed      : 0
% 2.18/1.23  
% 2.18/1.23  #Partial instantiations: 0
% 2.18/1.23  #Strategies tried      : 1
% 2.18/1.23  
% 2.18/1.23  Timing (in seconds)
% 2.18/1.23  ----------------------
% 2.18/1.24  Preprocessing        : 0.27
% 2.18/1.24  Parsing              : 0.15
% 2.18/1.24  CNF conversion       : 0.02
% 2.18/1.24  Main loop            : 0.20
% 2.18/1.24  Inferencing          : 0.09
% 2.18/1.24  Reduction            : 0.05
% 2.18/1.24  Demodulation         : 0.03
% 2.18/1.24  BG Simplification    : 0.01
% 2.18/1.24  Subsumption          : 0.03
% 2.18/1.24  Abstraction          : 0.01
% 2.18/1.24  MUC search           : 0.00
% 2.18/1.24  Cooper               : 0.00
% 2.18/1.24  Total                : 0.51
% 2.18/1.24  Index Insertion      : 0.00
% 2.18/1.24  Index Deletion       : 0.00
% 2.18/1.24  Index Matching       : 0.00
% 2.18/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
