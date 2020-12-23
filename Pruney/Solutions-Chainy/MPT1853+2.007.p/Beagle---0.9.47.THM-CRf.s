%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 135 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 364 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_128,plain,(
    ! [A_40,B_41] :
      ( ~ v2_struct_0(k1_tex_2(A_40,B_41))
      | ~ m1_subset_1(B_41,u1_struct_0(A_40))
      | ~ l1_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_131,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_128])).

tff(c_134,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_131])).

tff(c_135,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_134])).

tff(c_136,plain,(
    ! [A_42,B_43] :
      ( m1_pre_topc(k1_tex_2(A_42,B_43),A_42)
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_138,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_141,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_138])).

tff(c_142,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_141])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( ~ v2_struct_0(k1_tex_2(A_20,B_21))
      | ~ m1_subset_1(B_21,u1_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_47,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_50,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_47])).

tff(c_51,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_50])).

tff(c_68,plain,(
    ! [A_26,B_27] :
      ( m1_pre_topc(k1_tex_2(A_26,B_27),A_26)
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_70,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_73,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70])).

tff(c_74,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_73])).

tff(c_60,plain,(
    ! [A_24,B_25] :
      ( v7_struct_0(k1_tex_2(A_24,B_25))
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_66,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63])).

tff(c_67,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_66])).

tff(c_76,plain,(
    ! [B_30,A_31] :
      ( ~ v7_struct_0(B_30)
      | v1_tex_2(B_30,A_31)
      | v2_struct_0(B_30)
      | ~ m1_pre_topc(B_30,A_31)
      | ~ l1_pre_topc(A_31)
      | v7_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_82,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_42])).

tff(c_86,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74,c_67,c_82])).

tff(c_87,plain,(
    v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_51,c_86])).

tff(c_40,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_43,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40])).

tff(c_89,plain,(
    ! [A_34,B_35] :
      ( ~ v7_struct_0(A_34)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_34),B_35),u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l1_struct_0(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_95,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_43,c_89])).

tff(c_99,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_87,c_95])).

tff(c_100,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_99])).

tff(c_103,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_103])).

tff(c_109,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_143,plain,(
    ! [B_44,A_45] :
      ( ~ v1_tex_2(B_44,A_45)
      | v2_struct_0(B_44)
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v7_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_109,c_143])).

tff(c_149,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_142,c_146])).

tff(c_150,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_135,c_149])).

tff(c_157,plain,(
    ! [A_50,B_51] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_50),B_51),u1_struct_0(A_50))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_struct_0(A_50)
      | v7_struct_0(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_108,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_163,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_157,c_108])).

tff(c_167,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_163])).

tff(c_168,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_150,c_167])).

tff(c_171,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.21  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.07/1.21  
% 2.07/1.21  %Foreground sorts:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Background operators:
% 2.07/1.21  
% 2.07/1.21  
% 2.07/1.21  %Foreground operators:
% 2.07/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.07/1.21  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.07/1.21  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.07/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.07/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.21  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.07/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.21  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.07/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.21  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.07/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.21  
% 2.07/1.23  tff(f_138, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.07/1.23  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.07/1.23  tff(f_99, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.07/1.23  tff(f_85, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.07/1.23  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.07/1.23  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.07/1.23  tff(f_48, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.07/1.23  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.07/1.23  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.07/1.23  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.23  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.07/1.23  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.07/1.23  tff(c_128, plain, (![A_40, B_41]: (~v2_struct_0(k1_tex_2(A_40, B_41)) | ~m1_subset_1(B_41, u1_struct_0(A_40)) | ~l1_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.07/1.23  tff(c_131, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_128])).
% 2.07/1.23  tff(c_134, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_131])).
% 2.07/1.23  tff(c_135, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_134])).
% 2.07/1.23  tff(c_136, plain, (![A_42, B_43]: (m1_pre_topc(k1_tex_2(A_42, B_43), A_42) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.23  tff(c_138, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_136])).
% 2.07/1.23  tff(c_141, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_138])).
% 2.07/1.23  tff(c_142, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_141])).
% 2.07/1.23  tff(c_44, plain, (![A_20, B_21]: (~v2_struct_0(k1_tex_2(A_20, B_21)) | ~m1_subset_1(B_21, u1_struct_0(A_20)) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.07/1.23  tff(c_47, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_44])).
% 2.07/1.23  tff(c_50, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_47])).
% 2.07/1.23  tff(c_51, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_50])).
% 2.07/1.23  tff(c_68, plain, (![A_26, B_27]: (m1_pre_topc(k1_tex_2(A_26, B_27), A_26) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.07/1.23  tff(c_70, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.07/1.23  tff(c_73, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70])).
% 2.07/1.23  tff(c_74, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_73])).
% 2.07/1.23  tff(c_60, plain, (![A_24, B_25]: (v7_struct_0(k1_tex_2(A_24, B_25)) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.07/1.23  tff(c_63, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_60])).
% 2.07/1.23  tff(c_66, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63])).
% 2.07/1.23  tff(c_67, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_66])).
% 2.07/1.23  tff(c_76, plain, (![B_30, A_31]: (~v7_struct_0(B_30) | v1_tex_2(B_30, A_31) | v2_struct_0(B_30) | ~m1_pre_topc(B_30, A_31) | ~l1_pre_topc(A_31) | v7_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.23  tff(c_34, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.07/1.23  tff(c_42, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.07/1.23  tff(c_82, plain, (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_42])).
% 2.07/1.23  tff(c_86, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74, c_67, c_82])).
% 2.07/1.23  tff(c_87, plain, (v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_51, c_86])).
% 2.07/1.23  tff(c_40, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.07/1.23  tff(c_43, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_40])).
% 2.07/1.23  tff(c_89, plain, (![A_34, B_35]: (~v7_struct_0(A_34) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_34), B_35), u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l1_struct_0(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.23  tff(c_95, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_43, c_89])).
% 2.07/1.23  tff(c_99, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_87, c_95])).
% 2.07/1.23  tff(c_100, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_99])).
% 2.07/1.23  tff(c_103, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_100])).
% 2.07/1.23  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_103])).
% 2.07/1.23  tff(c_109, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.07/1.23  tff(c_143, plain, (![B_44, A_45]: (~v1_tex_2(B_44, A_45) | v2_struct_0(B_44) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45) | ~v7_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.23  tff(c_146, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_109, c_143])).
% 2.07/1.23  tff(c_149, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_142, c_146])).
% 2.07/1.23  tff(c_150, plain, (~v7_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_135, c_149])).
% 2.07/1.23  tff(c_157, plain, (![A_50, B_51]: (v1_subset_1(k6_domain_1(u1_struct_0(A_50), B_51), u1_struct_0(A_50)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_struct_0(A_50) | v7_struct_0(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.07/1.23  tff(c_108, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_34])).
% 2.07/1.23  tff(c_163, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_157, c_108])).
% 2.07/1.23  tff(c_167, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_163])).
% 2.07/1.23  tff(c_168, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_150, c_167])).
% 2.07/1.23  tff(c_171, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_168])).
% 2.07/1.23  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_171])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 18
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 1
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 2
% 2.07/1.23  #Demod        : 19
% 2.07/1.23  #Tautology    : 9
% 2.07/1.23  #SimpNegUnit  : 14
% 2.07/1.23  #BackRed      : 0
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.29
% 2.07/1.23  Parsing              : 0.17
% 2.07/1.23  CNF conversion       : 0.02
% 2.20/1.23  Main loop            : 0.16
% 2.20/1.23  Inferencing          : 0.07
% 2.20/1.23  Reduction            : 0.04
% 2.20/1.23  Demodulation         : 0.03
% 2.20/1.23  BG Simplification    : 0.01
% 2.20/1.23  Subsumption          : 0.02
% 2.20/1.23  Abstraction          : 0.01
% 2.20/1.23  MUC search           : 0.00
% 2.20/1.23  Cooper               : 0.00
% 2.20/1.23  Total                : 0.49
% 2.20/1.23  Index Insertion      : 0.00
% 2.20/1.23  Index Deletion       : 0.00
% 2.20/1.23  Index Matching       : 0.00
% 2.20/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
