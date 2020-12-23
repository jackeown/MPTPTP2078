%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:00 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   58 (  79 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  116 ( 375 expanded)
%              Number of equality atoms :    5 (  22 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( v1_compts_1(A)
                    & v8_pre_topc(B)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v5_pre_topc(C,A,B) )
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( v4_pre_topc(D,A)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                 => ( ( v5_pre_topc(D,A,C)
                      & k2_relset_1(u1_struct_0(A),u1_struct_0(C),D) = k2_struct_0(C)
                      & v2_compts_1(B,A) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(A),u1_struct_0(C),D,B),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12,plain,(
    v4_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    ! [B_41,A_42] :
      ( v2_compts_1(B_41,A_42)
      | ~ v4_pre_topc(B_41,A_42)
      | ~ v1_compts_1(A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_51,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ v1_compts_1('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_55,plain,(
    v2_compts_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_22,c_12,c_51])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_68,plain,(
    ! [A_45,C_46,D_47,B_48] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_45),u1_struct_0(C_46),D_47,B_48),C_46)
      | ~ v2_compts_1(B_48,A_45)
      | k2_relset_1(u1_struct_0(A_45),u1_struct_0(C_46),D_47) != k2_struct_0(C_46)
      | ~ v5_pre_topc(D_47,A_45,C_46)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45),u1_struct_0(C_46))))
      | ~ v1_funct_2(D_47,u1_struct_0(A_45),u1_struct_0(C_46))
      | ~ v1_funct_1(D_47)
      | ~ l1_pre_topc(C_46)
      | v2_struct_0(C_46)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_73,plain,(
    ! [B_48] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',B_48),'#skF_2')
      | ~ v2_compts_1(B_48,'#skF_1')
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_77,plain,(
    ! [B_48] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',B_48),'#skF_2')
      | ~ v2_compts_1(B_48,'#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_26,c_16,c_18,c_73])).

tff(c_78,plain,(
    ! [B_48] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',B_48),'#skF_2')
      | ~ v2_compts_1(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_77])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_20,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k7_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(B_2))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_43,A_44] :
      ( v4_pre_topc(B_43,A_44)
      | ~ v2_compts_1(B_43,A_44)
      | ~ v8_pre_topc(A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_54,A_55,C_56,D_57] :
      ( v4_pre_topc(k7_relset_1(A_54,u1_struct_0(A_55),C_56,D_57),A_55)
      | ~ v2_compts_1(k7_relset_1(A_54,u1_struct_0(A_55),C_56,D_57),A_55)
      | ~ v8_pre_topc(A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,u1_struct_0(A_55)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_86,plain,(
    ! [D_57] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_57),'#skF_2')
      | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_57),'#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_91,plain,(
    ! [D_58] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_58),'#skF_2')
      | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_58),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_20,c_86])).

tff(c_10,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_100,plain,(
    ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_10])).

tff(c_103,plain,
    ( ~ v2_compts_1('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_55,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.21  
% 2.08/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.21  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.08/1.21  
% 2.08/1.21  %Foreground sorts:
% 2.08/1.21  
% 2.08/1.21  
% 2.08/1.21  %Background operators:
% 2.08/1.21  
% 2.08/1.21  
% 2.08/1.21  %Foreground operators:
% 2.08/1.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.08/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.21  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.08/1.21  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 2.08/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.08/1.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.08/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.21  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.21  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.08/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.08/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.21  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 2.08/1.21  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.08/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.21  
% 2.08/1.23  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 2.08/1.23  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_compts_1(A) & v4_pre_topc(B, A)) => v2_compts_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_compts_1)).
% 2.08/1.23  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_compts_1)).
% 2.08/1.23  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.08/1.23  tff(f_42, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 2.08/1.23  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_22, plain, (v1_compts_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_12, plain, (v4_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_44, plain, (![B_41, A_42]: (v2_compts_1(B_41, A_42) | ~v4_pre_topc(B_41, A_42) | ~v1_compts_1(A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.08/1.23  tff(c_51, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v4_pre_topc('#skF_4', '#skF_1') | ~v1_compts_1('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.08/1.23  tff(c_55, plain, (v2_compts_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_22, c_12, c_51])).
% 2.08/1.23  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_26, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_16, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_18, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_68, plain, (![A_45, C_46, D_47, B_48]: (v2_compts_1(k7_relset_1(u1_struct_0(A_45), u1_struct_0(C_46), D_47, B_48), C_46) | ~v2_compts_1(B_48, A_45) | k2_relset_1(u1_struct_0(A_45), u1_struct_0(C_46), D_47)!=k2_struct_0(C_46) | ~v5_pre_topc(D_47, A_45, C_46) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45), u1_struct_0(C_46)))) | ~v1_funct_2(D_47, u1_struct_0(A_45), u1_struct_0(C_46)) | ~v1_funct_1(D_47) | ~l1_pre_topc(C_46) | v2_struct_0(C_46) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.08/1.23  tff(c_73, plain, (![B_48]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', B_48), '#skF_2') | ~v2_compts_1(B_48, '#skF_1') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_68])).
% 2.08/1.23  tff(c_77, plain, (![B_48]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', B_48), '#skF_2') | ~v2_compts_1(B_48, '#skF_1') | v2_struct_0('#skF_2') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_28, c_26, c_16, c_18, c_73])).
% 2.08/1.23  tff(c_78, plain, (![B_48]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', B_48), '#skF_2') | ~v2_compts_1(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_77])).
% 2.08/1.23  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_20, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k7_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(B_2)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.23  tff(c_56, plain, (![B_43, A_44]: (v4_pre_topc(B_43, A_44) | ~v2_compts_1(B_43, A_44) | ~v8_pre_topc(A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.23  tff(c_81, plain, (![A_54, A_55, C_56, D_57]: (v4_pre_topc(k7_relset_1(A_54, u1_struct_0(A_55), C_56, D_57), A_55) | ~v2_compts_1(k7_relset_1(A_54, u1_struct_0(A_55), C_56, D_57), A_55) | ~v8_pre_topc(A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, u1_struct_0(A_55)))))), inference(resolution, [status(thm)], [c_2, c_56])).
% 2.08/1.23  tff(c_86, plain, (![D_57]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_57), '#skF_2') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_57), '#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.08/1.23  tff(c_91, plain, (![D_58]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_58), '#skF_2') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_58), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_20, c_86])).
% 2.08/1.23  tff(c_10, plain, (~v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.08/1.23  tff(c_100, plain, (~v2_compts_1(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_91, c_10])).
% 2.08/1.23  tff(c_103, plain, (~v2_compts_1('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_78, c_100])).
% 2.08/1.23  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_55, c_103])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 13
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 0
% 2.08/1.23  #Demod        : 20
% 2.08/1.23  #Tautology    : 4
% 2.08/1.23  #SimpNegUnit  : 1
% 2.08/1.23  #BackRed      : 0
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.30
% 2.08/1.23  Parsing              : 0.17
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.16
% 2.08/1.23  Inferencing          : 0.07
% 2.08/1.23  Reduction            : 0.05
% 2.08/1.23  Demodulation         : 0.04
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.03
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.49
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
