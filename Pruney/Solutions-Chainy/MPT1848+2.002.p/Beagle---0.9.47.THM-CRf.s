%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 207 expanded)
%              Number of leaves         :   36 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 403 expanded)
%              Number of equality atoms :   15 (  86 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_60,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_12,plain,(
    ! [A_6] : g1_orders_2(A_6,k1_yellow_1(A_6)) = k2_yellow_1(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_7] : m1_subset_1(k1_yellow_1(A_7),k1_zfmisc_1(k2_zfmisc_1(A_7,A_7))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ! [A_41,B_42] :
      ( l1_orders_2(g1_orders_2(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_138,plain,(
    ! [A_7] : l1_orders_2(g1_orders_2(A_7,k1_yellow_1(A_7))) ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_141,plain,(
    ! [A_7] : l1_orders_2(k2_yellow_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    ! [A_8] : u1_struct_0(k2_yellow_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [B_35,A_36] :
      ( v1_subset_1(B_35,A_36)
      | B_35 = A_36
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_143,plain,(
    ! [A_44] :
      ( v1_subset_1(k2_struct_0(A_44),u1_struct_0(A_44))
      | u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_subset_1(k2_struct_0(A_2),u1_struct_0(A_2))
      | ~ l1_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_162,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_165,plain,(
    ! [A_7] : u1_struct_0(k2_yellow_1(A_7)) = k2_struct_0(k2_yellow_1(A_7)) ),
    inference(resolution,[status(thm)],[c_141,c_162])).

tff(c_167,plain,(
    ! [A_7] : k2_struct_0(k2_yellow_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_165])).

tff(c_92,plain,(
    ! [A_33] :
      ( m1_subset_1(k2_struct_0(A_33),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_8] :
      ( m1_subset_1(k2_struct_0(k2_yellow_1(A_8)),k1_zfmisc_1(A_8))
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_92])).

tff(c_168,plain,(
    ! [A_8] :
      ( m1_subset_1(A_8,k1_zfmisc_1(A_8))
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_98])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_298,plain,(
    ! [B_69,A_70] :
      ( v1_subset_1(u1_struct_0(B_69),u1_struct_0(A_70))
      | ~ m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v1_tex_2(B_69,A_70)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_314,plain,(
    ! [B_69] :
      ( v1_subset_1(u1_struct_0(B_69),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_69,'#skF_2')
      | ~ m1_pre_topc(B_69,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_298])).

tff(c_329,plain,(
    ! [B_71] :
      ( v1_subset_1(u1_struct_0(B_71),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_tex_2(B_71,'#skF_2')
      | ~ m1_pre_topc(B_71,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_314])).

tff(c_336,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_168,c_329])).

tff(c_346,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_336])).

tff(c_367,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_370,plain,(
    ~ l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_367])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_370])).

tff(c_376,plain,(
    l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_375,plain,(
    v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_83,plain,(
    ! [A_30] :
      ( ~ v1_subset_1(k2_struct_0(A_30),u1_struct_0(A_30))
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [A_8] :
      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(A_8)),A_8)
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_169,plain,(
    ! [A_8] :
      ( ~ v1_subset_1(A_8,A_8)
      | ~ l1_struct_0(k2_yellow_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_89])).

tff(c_384,plain,(
    ~ l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_375,c_169])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  %$ v1_tex_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.34  
% 2.56/1.34  %Foreground sorts:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Background operators:
% 2.56/1.34  
% 2.56/1.34  
% 2.56/1.34  %Foreground operators:
% 2.56/1.34  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.56/1.34  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.56/1.34  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.56/1.34  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.56/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.34  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.56/1.34  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.56/1.34  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.56/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.56/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.34  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.56/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.56/1.34  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.56/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.56/1.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.56/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.34  
% 2.56/1.35  tff(f_46, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 2.56/1.35  tff(f_56, axiom, (![A]: ((((v1_relat_2(k1_yellow_1(A)) & v4_relat_2(k1_yellow_1(A))) & v8_relat_2(k1_yellow_1(A))) & v1_partfun1(k1_yellow_1(A), A)) & m1_subset_1(k1_yellow_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 2.56/1.35  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (v1_orders_2(g1_orders_2(A, B)) & l1_orders_2(g1_orders_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 2.56/1.35  tff(f_44, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.56/1.35  tff(f_92, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.56/1.35  tff(f_60, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.56/1.35  tff(f_29, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.56/1.35  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.56/1.35  tff(f_34, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.56/1.35  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.56/1.35  tff(c_12, plain, (![A_6]: (g1_orders_2(A_6, k1_yellow_1(A_6))=k2_yellow_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.35  tff(c_22, plain, (![A_7]: (m1_subset_1(k1_yellow_1(A_7), k1_zfmisc_1(k2_zfmisc_1(A_7, A_7))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.35  tff(c_131, plain, (![A_41, B_42]: (l1_orders_2(g1_orders_2(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.56/1.35  tff(c_138, plain, (![A_7]: (l1_orders_2(g1_orders_2(A_7, k1_yellow_1(A_7))))), inference(resolution, [status(thm)], [c_22, c_131])).
% 2.56/1.35  tff(c_141, plain, (![A_7]: (l1_orders_2(k2_yellow_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_138])).
% 2.56/1.35  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.56/1.35  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.35  tff(c_40, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.35  tff(c_24, plain, (![A_8]: (u1_struct_0(k2_yellow_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.56/1.35  tff(c_2, plain, (![A_1]: (m1_subset_1(k2_struct_0(A_1), k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.35  tff(c_105, plain, (![B_35, A_36]: (v1_subset_1(B_35, A_36) | B_35=A_36 | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.35  tff(c_143, plain, (![A_44]: (v1_subset_1(k2_struct_0(A_44), u1_struct_0(A_44)) | u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(resolution, [status(thm)], [c_2, c_105])).
% 2.56/1.35  tff(c_4, plain, (![A_2]: (~v1_subset_1(k2_struct_0(A_2), u1_struct_0(A_2)) | ~l1_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.56/1.35  tff(c_156, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(resolution, [status(thm)], [c_143, c_4])).
% 2.56/1.35  tff(c_162, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_orders_2(A_48))), inference(resolution, [status(thm)], [c_10, c_156])).
% 2.56/1.35  tff(c_165, plain, (![A_7]: (u1_struct_0(k2_yellow_1(A_7))=k2_struct_0(k2_yellow_1(A_7)))), inference(resolution, [status(thm)], [c_141, c_162])).
% 2.56/1.35  tff(c_167, plain, (![A_7]: (k2_struct_0(k2_yellow_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_165])).
% 2.56/1.35  tff(c_92, plain, (![A_33]: (m1_subset_1(k2_struct_0(A_33), k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.35  tff(c_98, plain, (![A_8]: (m1_subset_1(k2_struct_0(k2_yellow_1(A_8)), k1_zfmisc_1(A_8)) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_92])).
% 2.56/1.35  tff(c_168, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_98])).
% 2.56/1.35  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.35  tff(c_42, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.56/1.35  tff(c_298, plain, (![B_69, A_70]: (v1_subset_1(u1_struct_0(B_69), u1_struct_0(A_70)) | ~m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_70))) | ~v1_tex_2(B_69, A_70) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.35  tff(c_314, plain, (![B_69]: (v1_subset_1(u1_struct_0(B_69), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_69, '#skF_2') | ~m1_pre_topc(B_69, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_298])).
% 2.56/1.35  tff(c_329, plain, (![B_71]: (v1_subset_1(u1_struct_0(B_71), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tex_2(B_71, '#skF_2') | ~m1_pre_topc(B_71, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_314])).
% 2.56/1.35  tff(c_336, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_168, c_329])).
% 2.56/1.35  tff(c_346, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_336])).
% 2.56/1.35  tff(c_367, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_346])).
% 2.56/1.35  tff(c_370, plain, (~l1_orders_2(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_367])).
% 2.56/1.35  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_370])).
% 2.56/1.35  tff(c_376, plain, (l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_346])).
% 2.56/1.35  tff(c_375, plain, (v1_subset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_346])).
% 2.56/1.35  tff(c_83, plain, (![A_30]: (~v1_subset_1(k2_struct_0(A_30), u1_struct_0(A_30)) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.56/1.35  tff(c_89, plain, (![A_8]: (~v1_subset_1(k2_struct_0(k2_yellow_1(A_8)), A_8) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_83])).
% 2.56/1.35  tff(c_169, plain, (![A_8]: (~v1_subset_1(A_8, A_8) | ~l1_struct_0(k2_yellow_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_89])).
% 2.56/1.35  tff(c_384, plain, (~l1_struct_0(k2_yellow_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_375, c_169])).
% 2.56/1.35  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_384])).
% 2.56/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  Inference rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Ref     : 0
% 2.56/1.35  #Sup     : 69
% 2.56/1.35  #Fact    : 0
% 2.56/1.35  #Define  : 0
% 2.56/1.35  #Split   : 3
% 2.56/1.35  #Chain   : 0
% 2.56/1.35  #Close   : 0
% 2.56/1.35  
% 2.56/1.35  Ordering : KBO
% 2.56/1.35  
% 2.56/1.35  Simplification rules
% 2.56/1.35  ----------------------
% 2.56/1.35  #Subsume      : 9
% 2.56/1.35  #Demod        : 40
% 2.56/1.35  #Tautology    : 18
% 2.56/1.35  #SimpNegUnit  : 0
% 2.56/1.35  #BackRed      : 2
% 2.56/1.35  
% 2.56/1.35  #Partial instantiations: 0
% 2.56/1.35  #Strategies tried      : 1
% 2.56/1.35  
% 2.56/1.35  Timing (in seconds)
% 2.56/1.35  ----------------------
% 2.56/1.36  Preprocessing        : 0.32
% 2.56/1.36  Parsing              : 0.17
% 2.56/1.36  CNF conversion       : 0.02
% 2.56/1.36  Main loop            : 0.27
% 2.56/1.36  Inferencing          : 0.10
% 2.56/1.36  Reduction            : 0.08
% 2.56/1.36  Demodulation         : 0.06
% 2.56/1.36  BG Simplification    : 0.02
% 2.56/1.36  Subsumption          : 0.05
% 2.56/1.36  Abstraction          : 0.01
% 2.56/1.36  MUC search           : 0.00
% 2.56/1.36  Cooper               : 0.00
% 2.56/1.36  Total                : 0.62
% 2.56/1.36  Index Insertion      : 0.00
% 2.56/1.36  Index Deletion       : 0.00
% 2.56/1.36  Index Matching       : 0.00
% 2.56/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
