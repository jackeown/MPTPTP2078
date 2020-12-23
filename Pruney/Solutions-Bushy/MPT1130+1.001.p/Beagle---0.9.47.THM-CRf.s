%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1130+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:27 EST 2020

% Result     : Theorem 13.53s
% Output     : CNFRefutation 13.85s
% Verified   : 
% Statistics : Number of formulae       :  346 (9723 expanded)
%              Number of leaves         :   33 (3295 expanded)
%              Depth                    :   25
%              Number of atoms          :  746 (22288 expanded)
%              Number of equality atoms :  114 (3713 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v4_pre_topc(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_63,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_200,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_46])).

tff(c_201,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_89,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_pre_topc(A_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_89])).

tff(c_94,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_92])).

tff(c_110,plain,(
    ! [A_35,B_36] :
      ( l1_pre_topc(g1_pre_topc(A_35,B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_117,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_110])).

tff(c_95,plain,(
    ! [A_32,B_33] :
      ( v1_pre_topc(g1_pre_topc(A_32,B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_95])).

tff(c_58,plain,(
    ! [A_15] :
      ( u1_struct_0(A_15) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_123,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_117,c_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_326,plain,(
    ! [C_59,A_60,D_61,B_62] :
      ( C_59 = A_60
      | g1_pre_topc(C_59,D_61) != g1_pre_topc(A_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_328,plain,(
    ! [A_1,A_60,B_62] :
      ( u1_struct_0(A_1) = A_60
      | g1_pre_topc(A_60,B_62) != A_1
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_326])).

tff(c_7900,plain,(
    ! [A_454,B_455] :
      ( u1_struct_0(g1_pre_topc(A_454,B_455)) = A_454
      | ~ m1_subset_1(B_455,k1_zfmisc_1(k1_zfmisc_1(A_454)))
      | ~ v1_pre_topc(g1_pre_topc(A_454,B_455))
      | ~ l1_pre_topc(g1_pre_topc(A_454,B_455)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_328])).

tff(c_7922,plain,
    ( u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_7900])).

tff(c_7942,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_7922])).

tff(c_18,plain,(
    ! [A_11] :
      ( m1_subset_1(k2_struct_0(A_11),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_81,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_52])).

tff(c_83,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_166,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_181,plain,(
    ! [A_11,C_44] :
      ( k7_subset_1(u1_struct_0(A_11),k2_struct_0(A_11),C_44) = k4_xboole_0(k2_struct_0(A_11),C_44)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_628,plain,(
    ! [A_92,B_93] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_92),k2_struct_0(A_92),B_93),A_92)
      | ~ v4_pre_topc(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_643,plain,(
    ! [A_11,C_44] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ v4_pre_topc(C_44,A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_628])).

tff(c_80,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_182,plain,(
    ! [C_45] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_45) = k4_xboole_0(k2_struct_0('#skF_1'),C_45) ),
    inference(resolution,[status(thm)],[c_80,c_166])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k7_subset_1(A_12,B_13,C_14),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    ! [C_45] :
      ( m1_subset_1(k4_xboole_0(k2_struct_0('#skF_1'),C_45),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_20])).

tff(c_194,plain,(
    ! [C_45] : m1_subset_1(k4_xboole_0(k2_struct_0('#skF_1'),C_45),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_188])).

tff(c_434,plain,(
    ! [B_78,A_79] :
      ( r2_hidden(B_78,u1_pre_topc(A_79))
      | ~ v3_pre_topc(B_78,A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_444,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_434])).

tff(c_457,plain,(
    ! [B_81] :
      ( r2_hidden(B_81,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_444])).

tff(c_482,plain,(
    ! [C_45] :
      ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_45),u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),C_45),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_194,c_457])).

tff(c_1617,plain,(
    ! [A_178,B_179] :
      ( u1_struct_0(g1_pre_topc(A_178,B_179)) = A_178
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k1_zfmisc_1(A_178)))
      | ~ v1_pre_topc(g1_pre_topc(A_178,B_179))
      | ~ l1_pre_topc(g1_pre_topc(A_178,B_179)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_328])).

tff(c_1639,plain,
    ( u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_1617])).

tff(c_1659,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_1639])).

tff(c_387,plain,(
    ! [B_75,A_76] :
      ( v3_pre_topc(B_75,A_76)
      | ~ r2_hidden(B_75,u1_pre_topc(A_76))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_397,plain,(
    ! [B_75] :
      ( v3_pre_topc(B_75,'#skF_1')
      | ~ r2_hidden(B_75,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_387])).

tff(c_407,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_1')
      | ~ r2_hidden(B_77,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_397])).

tff(c_432,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_407])).

tff(c_454,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_335,plain,(
    ! [D_63,B_64,C_65,A_66] :
      ( D_63 = B_64
      | g1_pre_topc(C_65,D_63) != g1_pre_topc(A_66,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_337,plain,(
    ! [A_1,B_64,A_66] :
      ( u1_pre_topc(A_1) = B_64
      | g1_pre_topc(A_66,B_64) != A_1
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_66)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_335])).

tff(c_1126,plain,(
    ! [A_156,B_157] :
      ( u1_pre_topc(g1_pre_topc(A_156,B_157)) = B_157
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k1_zfmisc_1(A_156)))
      | ~ v1_pre_topc(g1_pre_topc(A_156,B_157))
      | ~ l1_pre_topc(g1_pre_topc(A_156,B_157)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_337])).

tff(c_1148,plain,
    ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_1126])).

tff(c_1168,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_1148])).

tff(c_453,plain,(
    ! [A_11] :
      ( r2_hidden(k2_struct_0(A_11),u1_pre_topc(A_11))
      | ~ v3_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_434])).

tff(c_1689,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_453])).

tff(c_1708,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1659,c_1168,c_1689])).

tff(c_1709,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_1708])).

tff(c_2057,plain,(
    ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1709])).

tff(c_2060,plain,(
    ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_2057])).

tff(c_2064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_2060])).

tff(c_2066,plain,(
    l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1709])).

tff(c_1666,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_123])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v3_pre_topc(B_5,A_3)
      | ~ r2_hidden(B_5,u1_pre_topc(A_3))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1748,plain,(
    ! [B_5] :
      ( v3_pre_topc(B_5,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ r2_hidden(B_5,u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1666,c_6])).

tff(c_2245,plain,(
    ! [B_202] :
      ( v3_pre_topc(B_202,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ r2_hidden(B_202,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1168,c_1748])).

tff(c_499,plain,(
    ! [B_84,A_85] :
      ( v4_pre_topc(B_84,A_85)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_85),k2_struct_0(A_85),B_84),A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_505,plain,(
    ! [C_44,A_11] :
      ( v4_pre_topc(C_44,A_11)
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_499])).

tff(c_2255,plain,(
    ! [C_44] :
      ( v4_pre_topc(C_44,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ r2_hidden(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_2245,c_505])).

tff(c_6677,plain,(
    ! [C_350] :
      ( v4_pre_topc(C_350,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_350,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_350),u1_pre_topc('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1659,c_1659,c_2066,c_117,c_1666,c_2255])).

tff(c_40,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v4_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_385,plain,
    ( v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v4_pre_topc('#skF_3',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_123,c_63,c_63,c_40])).

tff(c_386,plain,(
    ~ v4_pre_topc('#skF_3',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_6680,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_3'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6677,c_386])).

tff(c_6683,plain,(
    ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_3'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_6680])).

tff(c_6687,plain,(
    ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_482,c_6683])).

tff(c_6690,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_643,c_6687])).

tff(c_6697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_201,c_63,c_83,c_6690])).

tff(c_6699,plain,(
    v4_pre_topc('#skF_3',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v4_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6701,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6699,c_63,c_123,c_63,c_63,c_36])).

tff(c_6702,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_6701])).

tff(c_7949,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7942,c_6702])).

tff(c_7957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_7949])).

tff(c_7958,plain,
    ( ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6701])).

tff(c_7960,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7958])).

tff(c_8747,plain,(
    ! [A_548,B_549] :
      ( u1_pre_topc(g1_pre_topc(A_548,B_549)) = B_549
      | ~ m1_subset_1(B_549,k1_zfmisc_1(k1_zfmisc_1(A_548)))
      | ~ v1_pre_topc(g1_pre_topc(A_548,B_549))
      | ~ l1_pre_topc(g1_pre_topc(A_548,B_549)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_337])).

tff(c_8763,plain,
    ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_8747])).

tff(c_8779,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_8763])).

tff(c_24,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8819,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8779,c_24])).

tff(c_8843,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_123,c_8819])).

tff(c_8810,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8779,c_2])).

tff(c_8837,plain,(
    g1_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_8810])).

tff(c_28,plain,(
    ! [C_21,A_17,D_22,B_18] :
      ( C_21 = A_17
      | g1_pre_topc(C_21,D_22) != g1_pre_topc(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9131,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8837,c_28])).

tff(c_9141,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8843,c_9131])).

tff(c_9302,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9141])).

tff(c_7959,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_6701])).

tff(c_38,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v4_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7962,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6699,c_63,c_123,c_63,c_123,c_63,c_38])).

tff(c_7963,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_7962])).

tff(c_7968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7959,c_7963])).

tff(c_7969,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_7962])).

tff(c_9325,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9302,c_7969])).

tff(c_9338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7960,c_9325])).

tff(c_9339,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_7958])).

tff(c_9340,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7958])).

tff(c_6698,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_9455,plain,(
    v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7959,c_6698])).

tff(c_9341,plain,(
    ! [B_577,A_578] :
      ( r2_hidden(B_577,u1_pre_topc(A_578))
      | ~ v3_pre_topc(B_577,A_578)
      | ~ m1_subset_1(B_577,k1_zfmisc_1(u1_struct_0(A_578)))
      | ~ l1_pre_topc(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9351,plain,(
    ! [B_577] :
      ( r2_hidden(B_577,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_577,'#skF_1')
      | ~ m1_subset_1(B_577,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_9341])).

tff(c_9419,plain,(
    ! [B_583] :
      ( r2_hidden(B_583,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_583,'#skF_1')
      | ~ m1_subset_1(B_583,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9351])).

tff(c_9452,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_9419])).

tff(c_9457,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9452])).

tff(c_9399,plain,(
    ! [B_581,A_582] :
      ( v3_pre_topc(B_581,A_582)
      | ~ r2_hidden(B_581,u1_pre_topc(A_582))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ l1_pre_topc(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9409,plain,(
    ! [B_581] :
      ( v3_pre_topc(B_581,'#skF_1')
      | ~ r2_hidden(B_581,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_9399])).

tff(c_9474,plain,(
    ! [B_588] :
      ( v3_pre_topc(B_588,'#skF_1')
      | ~ r2_hidden(B_588,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_588,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9409])).

tff(c_9499,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_9474])).

tff(c_9513,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_9457,c_9499])).

tff(c_10234,plain,(
    ! [A_682,B_683] :
      ( u1_struct_0(g1_pre_topc(A_682,B_683)) = A_682
      | ~ m1_subset_1(B_683,k1_zfmisc_1(k1_zfmisc_1(A_682)))
      | ~ v1_pre_topc(g1_pre_topc(A_682,B_683))
      | ~ l1_pre_topc(g1_pre_topc(A_682,B_683)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_328])).

tff(c_10250,plain,
    ( u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_10234])).

tff(c_10266,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_10250])).

tff(c_289,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_302,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_289])).

tff(c_10274,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10266,c_302])).

tff(c_10283,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10266,c_123])).

tff(c_10365,plain,
    ( g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10283,c_2])).

tff(c_10402,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_10365])).

tff(c_26,plain,(
    ! [D_22,B_18,C_21,A_17] :
      ( D_22 = B_18
      | g1_pre_topc(C_21,D_22) != g1_pre_topc(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_11004,plain,(
    ! [D_22,C_21] :
      ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = D_22
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22)
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10402,c_26])).

tff(c_11016,plain,(
    ! [D_22,C_21] :
      ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = D_22
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10274,c_11004])).

tff(c_11229,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11016])).

tff(c_9360,plain,(
    ! [A_11] :
      ( r2_hidden(k2_struct_0(A_11),u1_pre_topc(A_11))
      | ~ v3_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_9341])).

tff(c_11266,plain,
    ( r2_hidden(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11229,c_9360])).

tff(c_11300,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_10266,c_10266,c_11266])).

tff(c_11301,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_9513,c_11300])).

tff(c_11382,plain,(
    ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11301])).

tff(c_11385,plain,(
    ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_11382])).

tff(c_11389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_11385])).

tff(c_11391,plain,(
    l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_11301])).

tff(c_9459,plain,(
    ! [A_585,B_586] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_585),k2_struct_0(A_585),B_586),A_585)
      | ~ v4_pre_topc(B_586,A_585)
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9465,plain,(
    ! [A_11,C_44] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ v4_pre_topc(C_44,A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_9459])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( r2_hidden(B_5,u1_pre_topc(A_3))
      | ~ v3_pre_topc(B_5,A_3)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10356,plain,(
    ! [B_5] :
      ( r2_hidden(B_5,u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ v3_pre_topc(B_5,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10283,c_8])).

tff(c_10397,plain,(
    ! [B_5] :
      ( r2_hidden(B_5,u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ v3_pre_topc(B_5,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_10356])).

tff(c_17523,plain,(
    ! [B_911] :
      ( r2_hidden(B_911,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_911,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_911,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11229,c_10397])).

tff(c_17537,plain,(
    ! [C_44] :
      ( r2_hidden(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v4_pre_topc(C_44,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_9465,c_17523])).

tff(c_17617,plain,(
    ! [C_917] :
      ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_917),u1_pre_topc('#skF_1'))
      | ~ v4_pre_topc(C_917,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_917,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11391,c_117,c_10283,c_194,c_10266,c_10266,c_17537])).

tff(c_17623,plain,
    ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_9455,c_17617])).

tff(c_17630,plain,(
    r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9340,c_17623])).

tff(c_9509,plain,(
    ! [C_45] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),C_45),'#skF_1')
      | ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_45),u1_pre_topc('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_194,c_9474])).

tff(c_17637,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17630,c_9509])).

tff(c_9542,plain,(
    ! [B_593,A_594] :
      ( v4_pre_topc(B_593,A_594)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_594),k2_struct_0(A_594),B_593),A_594)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ l1_pre_topc(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9551,plain,(
    ! [C_44,A_11] :
      ( v4_pre_topc(C_44,A_11)
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_9542])).

tff(c_17640,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_17637,c_9551])).

tff(c_17646,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_9340,c_63,c_17640])).

tff(c_17648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9339,c_17646])).

tff(c_17650,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_17683,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_42])).

tff(c_17684,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_17650,c_17683])).

tff(c_17685,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17684])).

tff(c_17747,plain,(
    ! [D_928,B_929,C_930,A_931] :
      ( D_928 = B_929
      | g1_pre_topc(C_930,D_928) != g1_pre_topc(A_931,B_929)
      | ~ m1_subset_1(B_929,k1_zfmisc_1(k1_zfmisc_1(A_931))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_17749,plain,(
    ! [A_1,B_929,A_931] :
      ( u1_pre_topc(A_1) = B_929
      | g1_pre_topc(A_931,B_929) != A_1
      | ~ m1_subset_1(B_929,k1_zfmisc_1(k1_zfmisc_1(A_931)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17747])).

tff(c_18436,plain,(
    ! [A_1009,B_1010] :
      ( u1_pre_topc(g1_pre_topc(A_1009,B_1010)) = B_1010
      | ~ m1_subset_1(B_1010,k1_zfmisc_1(k1_zfmisc_1(A_1009)))
      | ~ v1_pre_topc(g1_pre_topc(A_1009,B_1010))
      | ~ l1_pre_topc(g1_pre_topc(A_1009,B_1010)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_17749])).

tff(c_18452,plain,
    ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_18436])).

tff(c_18468,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_18452])).

tff(c_18508,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18468,c_24])).

tff(c_18532,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_123,c_18508])).

tff(c_18499,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18468,c_2])).

tff(c_18526,plain,(
    g1_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_18499])).

tff(c_18805,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18526,c_28])).

tff(c_18815,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18532,c_18805])).

tff(c_18920,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18815])).

tff(c_44,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_17796,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_123,c_63,c_44])).

tff(c_17797,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_17650,c_17796])).

tff(c_18939,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18920,c_17797])).

tff(c_17649,plain,(
    v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_17819,plain,(
    ! [B_942,A_943] :
      ( r2_hidden(B_942,u1_pre_topc(A_943))
      | ~ v3_pre_topc(B_942,A_943)
      | ~ m1_subset_1(B_942,k1_zfmisc_1(u1_struct_0(A_943)))
      | ~ l1_pre_topc(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17829,plain,(
    ! [B_942] :
      ( r2_hidden(B_942,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_942,'#skF_1')
      | ~ m1_subset_1(B_942,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_17819])).

tff(c_17839,plain,(
    ! [B_944] :
      ( r2_hidden(B_944,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_944,'#skF_1')
      | ~ m1_subset_1(B_944,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17829])).

tff(c_17852,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_17839])).

tff(c_17853,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17852])).

tff(c_17854,plain,(
    ! [B_945,A_946] :
      ( v3_pre_topc(B_945,A_946)
      | ~ r2_hidden(B_945,u1_pre_topc(A_946))
      | ~ m1_subset_1(B_945,k1_zfmisc_1(u1_struct_0(A_946)))
      | ~ l1_pre_topc(A_946) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17864,plain,(
    ! [B_945] :
      ( v3_pre_topc(B_945,'#skF_1')
      | ~ r2_hidden(B_945,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_945,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_17854])).

tff(c_17874,plain,(
    ! [B_947] :
      ( v3_pre_topc(B_947,'#skF_1')
      | ~ r2_hidden(B_947,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_947,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_17864])).

tff(c_17884,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_17874])).

tff(c_17889,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_17853,c_17884])).

tff(c_17838,plain,(
    ! [A_11] :
      ( r2_hidden(k2_struct_0(A_11),u1_pre_topc(A_11))
      | ~ v3_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_17819])).

tff(c_18964,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18920,c_17838])).

tff(c_18983,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_18920,c_18468,c_18964])).

tff(c_18984,plain,
    ( ~ v3_pre_topc(k2_struct_0('#skF_1'),g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_17889,c_18983])).

tff(c_19262,plain,(
    ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_18984])).

tff(c_19265,plain,(
    ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_19262])).

tff(c_19269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_19265])).

tff(c_19271,plain,(
    l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_18984])).

tff(c_18940,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18920,c_123])).

tff(c_18082,plain,(
    ! [A_965,B_966] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_965),k2_struct_0(A_965),B_966),A_965)
      | ~ v4_pre_topc(B_966,A_965)
      | ~ m1_subset_1(B_966,k1_zfmisc_1(u1_struct_0(A_965)))
      | ~ l1_pre_topc(A_965) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18097,plain,(
    ! [A_11,C_44] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ v4_pre_topc(C_44,A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_18082])).

tff(c_19070,plain,(
    ! [B_5] :
      ( r2_hidden(B_5,u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ v3_pre_topc(B_5,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18940,c_8])).

tff(c_19846,plain,(
    ! [B_1075] :
      ( r2_hidden(B_1075,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_1075,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_1075,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_18468,c_19070])).

tff(c_19853,plain,(
    ! [C_44] :
      ( r2_hidden(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_44),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v4_pre_topc(C_44,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_18097,c_19846])).

tff(c_24821,plain,(
    ! [C_1243] :
      ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_1243),u1_pre_topc('#skF_1'))
      | ~ v4_pre_topc(C_1243,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_1243,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19271,c_117,c_18940,c_194,c_18920,c_18920,c_19853])).

tff(c_24827,plain,
    ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_17649,c_24821])).

tff(c_24831,plain,(
    r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18939,c_24827])).

tff(c_17885,plain,(
    ! [C_45] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),C_45),'#skF_1')
      | ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_45),u1_pre_topc('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_194,c_17874])).

tff(c_24835,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24831,c_17885])).

tff(c_17964,plain,(
    ! [B_953,A_954] :
      ( v4_pre_topc(B_953,A_954)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_954),k2_struct_0(A_954),B_953),A_954)
      | ~ m1_subset_1(B_953,k1_zfmisc_1(u1_struct_0(A_954)))
      | ~ l1_pre_topc(A_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17973,plain,(
    ! [C_44,A_11] :
      ( v4_pre_topc(C_44,A_11)
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_44),A_11)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_17964])).

tff(c_24838,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24835,c_17973])).

tff(c_24844,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_18939,c_63,c_24838])).

tff(c_24846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17685,c_24844])).

tff(c_24847,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_17684])).

tff(c_24853,plain,(
    ! [C_1244,A_1245,D_1246,B_1247] :
      ( C_1244 = A_1245
      | g1_pre_topc(C_1244,D_1246) != g1_pre_topc(A_1245,B_1247)
      | ~ m1_subset_1(B_1247,k1_zfmisc_1(k1_zfmisc_1(A_1245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24855,plain,(
    ! [A_1,A_1245,B_1247] :
      ( u1_struct_0(A_1) = A_1245
      | g1_pre_topc(A_1245,B_1247) != A_1
      | ~ m1_subset_1(B_1247,k1_zfmisc_1(k1_zfmisc_1(A_1245)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24853])).

tff(c_25663,plain,(
    ! [A_1340,B_1341] :
      ( u1_struct_0(g1_pre_topc(A_1340,B_1341)) = A_1340
      | ~ m1_subset_1(B_1341,k1_zfmisc_1(k1_zfmisc_1(A_1340)))
      | ~ v1_pre_topc(g1_pre_topc(A_1340,B_1341))
      | ~ l1_pre_topc(g1_pre_topc(A_1340,B_1341)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24855])).

tff(c_25679,plain,
    ( u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_25663])).

tff(c_25695,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_102,c_123,c_25679])).

tff(c_24876,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_44])).

tff(c_24877,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_17650,c_24876])).

tff(c_24901,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_24877])).

tff(c_25706,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25695,c_24901])).

tff(c_25709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24847,c_25706])).

tff(c_25711,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_25723,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48])).

tff(c_25724,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_25711,c_25723])).

tff(c_25725,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_25724])).

tff(c_25712,plain,(
    ! [A_1342] :
      ( m1_subset_1(u1_pre_topc(A_1342),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1342))))
      | ~ l1_pre_topc(A_1342) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25715,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_25712])).

tff(c_25717,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_25715])).

tff(c_25735,plain,(
    ! [A_1345,B_1346] :
      ( l1_pre_topc(g1_pre_topc(A_1345,B_1346))
      | ~ m1_subset_1(B_1346,k1_zfmisc_1(k1_zfmisc_1(A_1345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25742,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_25735])).

tff(c_25747,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25742,c_58])).

tff(c_25726,plain,(
    ! [A_1343,B_1344] :
      ( v1_pre_topc(g1_pre_topc(A_1343,B_1344))
      | ~ m1_subset_1(B_1344,k1_zfmisc_1(k1_zfmisc_1(A_1343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_25733,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_25726])).

tff(c_25972,plain,(
    ! [D_1372,B_1373,C_1374,A_1375] :
      ( D_1372 = B_1373
      | g1_pre_topc(C_1374,D_1372) != g1_pre_topc(A_1375,B_1373)
      | ~ m1_subset_1(B_1373,k1_zfmisc_1(k1_zfmisc_1(A_1375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_25974,plain,(
    ! [A_1,B_1373,A_1375] :
      ( u1_pre_topc(A_1) = B_1373
      | g1_pre_topc(A_1375,B_1373) != A_1
      | ~ m1_subset_1(B_1373,k1_zfmisc_1(k1_zfmisc_1(A_1375)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25972])).

tff(c_26652,plain,(
    ! [A_1453,B_1454] :
      ( u1_pre_topc(g1_pre_topc(A_1453,B_1454)) = B_1454
      | ~ m1_subset_1(B_1454,k1_zfmisc_1(k1_zfmisc_1(A_1453)))
      | ~ v1_pre_topc(g1_pre_topc(A_1453,B_1454))
      | ~ l1_pre_topc(g1_pre_topc(A_1453,B_1454)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_25974])).

tff(c_26668,plain,
    ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_26652])).

tff(c_26684,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25742,c_25733,c_26668])).

tff(c_26724,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26684,c_24])).

tff(c_26748,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25742,c_25747,c_26724])).

tff(c_26715,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26684,c_2])).

tff(c_26742,plain,(
    g1_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25742,c_25733,c_25747,c_26715])).

tff(c_26995,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26742,c_28])).

tff(c_27005,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26748,c_26995])).

tff(c_27134,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_27005])).

tff(c_50,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_25764,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_50])).

tff(c_25765,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_25711,c_25764])).

tff(c_25914,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25747,c_25765])).

tff(c_27168,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27134,c_25914])).

tff(c_25710,plain,(
    v4_pre_topc('#skF_2',g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_25933,plain,
    ( m1_subset_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25747,c_18])).

tff(c_27142,plain,(
    ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_25933])).

tff(c_27145,plain,(
    ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_27142])).

tff(c_27149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25742,c_27145])).

tff(c_27151,plain,(
    l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_25933])).

tff(c_27169,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27134,c_25747])).

tff(c_25787,plain,(
    ! [A_1350,B_1351,C_1352] :
      ( k7_subset_1(A_1350,B_1351,C_1352) = k4_xboole_0(B_1351,C_1352)
      | ~ m1_subset_1(B_1351,k1_zfmisc_1(A_1350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_25800,plain,(
    ! [C_1352] : k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),C_1352) = k4_xboole_0(k2_struct_0('#skF_1'),C_1352) ),
    inference(resolution,[status(thm)],[c_80,c_25787])).

tff(c_25812,plain,(
    ! [A_1354,B_1355,C_1356] :
      ( m1_subset_1(k7_subset_1(A_1354,B_1355,C_1356),k1_zfmisc_1(A_1354))
      | ~ m1_subset_1(B_1355,k1_zfmisc_1(A_1354)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25825,plain,(
    ! [C_1352] :
      ( m1_subset_1(k4_xboole_0(k2_struct_0('#skF_1'),C_1352),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25800,c_25812])).

tff(c_25830,plain,(
    ! [C_1352] : m1_subset_1(k4_xboole_0(k2_struct_0('#skF_1'),C_1352),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_25825])).

tff(c_25802,plain,(
    ! [A_11,C_1352] :
      ( k7_subset_1(u1_struct_0(A_11),k2_struct_0(A_11),C_1352) = k4_xboole_0(k2_struct_0(A_11),C_1352)
      | ~ l1_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_25787])).

tff(c_26080,plain,(
    ! [A_1391,B_1392] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_1391),k2_struct_0(A_1391),B_1392),A_1391)
      | ~ v4_pre_topc(B_1392,A_1391)
      | ~ m1_subset_1(B_1392,k1_zfmisc_1(u1_struct_0(A_1391)))
      | ~ l1_pre_topc(A_1391) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26086,plain,(
    ! [A_11,C_1352] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_1352),A_11)
      | ~ v4_pre_topc(C_1352,A_11)
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25802,c_26080])).

tff(c_27359,plain,(
    ! [B_5] :
      ( r2_hidden(B_5,u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | ~ v3_pre_topc(B_5,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27169,c_8])).

tff(c_28360,plain,(
    ! [B_1533] :
      ( r2_hidden(B_1533,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_1533,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(B_1533,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25742,c_26684,c_27359])).

tff(c_28364,plain,(
    ! [C_1352] :
      ( r2_hidden(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_1352),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(k4_xboole_0(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),C_1352),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ v4_pre_topc(C_1352,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26086,c_28360])).

tff(c_32822,plain,(
    ! [C_1684] :
      ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_1684),u1_pre_topc('#skF_1'))
      | ~ v4_pre_topc(C_1684,g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_subset_1(C_1684,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27151,c_25742,c_27169,c_25830,c_27134,c_27134,c_28364])).

tff(c_32828,plain,
    ( r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25710,c_32822])).

tff(c_32832,plain,(
    r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27168,c_32828])).

tff(c_26060,plain,(
    ! [B_1389,A_1390] :
      ( v3_pre_topc(B_1389,A_1390)
      | ~ r2_hidden(B_1389,u1_pre_topc(A_1390))
      | ~ m1_subset_1(B_1389,k1_zfmisc_1(u1_struct_0(A_1390)))
      | ~ l1_pre_topc(A_1390) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26070,plain,(
    ! [B_1389] :
      ( v3_pre_topc(B_1389,'#skF_1')
      | ~ r2_hidden(B_1389,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_1389,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_26060])).

tff(c_26094,plain,(
    ! [B_1393] :
      ( v3_pre_topc(B_1393,'#skF_1')
      | ~ r2_hidden(B_1393,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_1393,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26070])).

tff(c_26105,plain,(
    ! [C_1352] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),C_1352),'#skF_1')
      | ~ r2_hidden(k4_xboole_0(k2_struct_0('#skF_1'),C_1352),u1_pre_topc('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_25830,c_26094])).

tff(c_32836,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32832,c_26105])).

tff(c_26226,plain,(
    ! [B_1399,A_1400] :
      ( v4_pre_topc(B_1399,A_1400)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_1400),k2_struct_0(A_1400),B_1399),A_1400)
      | ~ m1_subset_1(B_1399,k1_zfmisc_1(u1_struct_0(A_1400)))
      | ~ l1_pre_topc(A_1400) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26241,plain,(
    ! [C_1352,A_11] :
      ( v4_pre_topc(C_1352,A_11)
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(A_11),C_1352),A_11)
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ l1_struct_0(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25802,c_26226])).

tff(c_32839,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32836,c_26241])).

tff(c_32845,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_27168,c_63,c_32839])).

tff(c_32847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25725,c_32845])).

tff(c_32848,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_25724])).

tff(c_32866,plain,(
    ! [A_1688,B_1689] :
      ( l1_pre_topc(g1_pre_topc(A_1688,B_1689))
      | ~ m1_subset_1(B_1689,k1_zfmisc_1(k1_zfmisc_1(A_1688))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32873,plain,(
    l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_32866])).

tff(c_32878,plain,(
    u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32873,c_58])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_pre_topc(g1_pre_topc(A_9,B_10))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32858,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_16])).

tff(c_32990,plain,(
    ! [D_1702,B_1703,C_1704,A_1705] :
      ( D_1702 = B_1703
      | g1_pre_topc(C_1704,D_1702) != g1_pre_topc(A_1705,B_1703)
      | ~ m1_subset_1(B_1703,k1_zfmisc_1(k1_zfmisc_1(A_1705))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32992,plain,(
    ! [A_1,B_1703,A_1705] :
      ( u1_pre_topc(A_1) = B_1703
      | g1_pre_topc(A_1705,B_1703) != A_1
      | ~ m1_subset_1(B_1703,k1_zfmisc_1(k1_zfmisc_1(A_1705)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32990])).

tff(c_33777,plain,(
    ! [A_1795,B_1796] :
      ( u1_pre_topc(g1_pre_topc(A_1795,B_1796)) = B_1796
      | ~ m1_subset_1(B_1796,k1_zfmisc_1(k1_zfmisc_1(A_1795)))
      | ~ v1_pre_topc(g1_pre_topc(A_1795,B_1796))
      | ~ l1_pre_topc(g1_pre_topc(A_1795,B_1796)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_32992])).

tff(c_33793,plain,
    ( u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_25717,c_33777])).

tff(c_33809,plain,(
    u1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32873,c_32858,c_33793])).

tff(c_33849,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33809,c_24])).

tff(c_33873,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32873,c_32878,c_33849])).

tff(c_33840,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_33809,c_2])).

tff(c_33867,plain,(
    g1_pre_topc(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32873,c_32858,c_32878,c_33840])).

tff(c_34157,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33867,c_28])).

tff(c_34169,plain,(
    ! [C_21,D_22] :
      ( k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = C_21
      | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != g1_pre_topc(C_21,D_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33873,c_34157])).

tff(c_34297,plain,(
    k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_34169])).

tff(c_32921,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_50])).

tff(c_32922,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_25711,c_32921])).

tff(c_33040,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0(g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32878,c_32922])).

tff(c_34316,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34297,c_33040])).

tff(c_34324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32848,c_34316])).

%------------------------------------------------------------------------------
