%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1133+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 709 expanded)
%              Number of leaves         :   27 ( 257 expanded)
%              Depth                    :   14
%              Number of atoms          :  268 (2957 expanded)
%              Number of equality atoms :   21 ( 345 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_67,plain,(
    ! [A_57] :
      ( m1_subset_1(u1_pre_topc(A_57),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57))))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [A_57] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_57),u1_pre_topc(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_10,plain,(
    ! [A_5] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [A_57] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_57),u1_pre_topc(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_67,c_6])).

tff(c_8,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_123,plain,(
    ! [C_62,A_63,D_64,B_65] :
      ( C_62 = A_63
      | g1_pre_topc(C_62,D_64) != g1_pre_topc(A_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [A_1,A_63,B_65] :
      ( u1_struct_0(A_1) = A_63
      | g1_pre_topc(A_63,B_65) != A_1
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_63)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_569,plain,(
    ! [A_121,B_122] :
      ( u1_struct_0(g1_pre_topc(A_121,B_122)) = A_121
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k1_zfmisc_1(A_121)))
      | ~ v1_pre_topc(g1_pre_topc(A_121,B_122))
      | ~ l1_pre_topc(g1_pre_topc(A_121,B_122)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_700,plain,(
    ! [A_135] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135))) = u1_struct_0(A_135)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_8,c_569])).

tff(c_711,plain,(
    ! [A_136] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_136),u1_pre_topc(A_136))) = u1_struct_0(A_136)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_136),u1_pre_topc(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_75,c_700])).

tff(c_742,plain,(
    ! [A_137] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_137),u1_pre_topc(A_137))) = u1_struct_0(A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_74,c_711])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_802,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_28])).

tff(c_840,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_802])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_55,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_59,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_30,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_823,plain,
    ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_30])).

tff(c_844,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_823])).

tff(c_195,plain,(
    ! [A_85,B_86] :
      ( u1_struct_0(g1_pre_topc(A_85,B_86)) = A_85
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ v1_pre_topc(g1_pre_topc(A_85,B_86))
      | ~ l1_pre_topc(g1_pre_topc(A_85,B_86)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_215,plain,(
    ! [A_92] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92))) = u1_struct_0(A_92)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_195])).

tff(c_223,plain,(
    ! [A_93] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93))) = u1_struct_0(A_93)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_75,c_215])).

tff(c_231,plain,(
    ! [A_94] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94))) = u1_struct_0(A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_74,c_223])).

tff(c_282,plain,
    ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_30])).

tff(c_300,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_282])).

tff(c_261,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_28])).

tff(c_296,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_261])).

tff(c_48,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_137,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54])).

tff(c_138,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_56])).

tff(c_205,plain,(
    ! [D_89,A_90,B_91] :
      ( v5_pre_topc(D_89,A_90,B_91)
      | ~ v5_pre_topc(D_89,A_90,g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90),u1_struct_0(g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91))))))
      | ~ v1_funct_2(D_89,u1_struct_0(A_90),u1_struct_0(g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91))))
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90),u1_struct_0(B_91))))
      | ~ v1_funct_2(D_89,u1_struct_0(A_90),u1_struct_0(B_91))
      | ~ v1_funct_1(D_89)
      | ~ l1_pre_topc(B_91)
      | ~ v2_pre_topc(B_91)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_208,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_214,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_32,c_30,c_138,c_208])).

tff(c_433,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_296,c_214])).

tff(c_434,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_440,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_434])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_440])).

tff(c_447,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_454,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_460,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_454])).

tff(c_466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_460])).

tff(c_467,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_474,plain,(
    ! [D_101,A_102,B_103] :
      ( v5_pre_topc(D_101,A_102,B_103)
      | ~ v5_pre_topc(D_101,g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102)),B_103)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102))),u1_struct_0(B_103))))
      | ~ v1_funct_2(D_101,u1_struct_0(g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102))),u1_struct_0(B_103))
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(D_101,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(D_101)
      | ~ l1_pre_topc(B_103)
      | ~ v2_pre_topc(B_103)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_477,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_296,c_474])).

tff(c_495,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_32,c_55,c_59,c_300,c_477])).

tff(c_496,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_495])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_496])).

tff(c_510,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_20,plain,(
    ! [D_26,A_12,B_20] :
      ( v5_pre_topc(D_26,g1_pre_topc(u1_struct_0(A_12),u1_pre_topc(A_12)),B_20)
      | ~ v5_pre_topc(D_26,A_12,B_20)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12),u1_pre_topc(A_12))),u1_struct_0(B_20))))
      | ~ v1_funct_2(D_26,u1_struct_0(g1_pre_topc(u1_struct_0(A_12),u1_pre_topc(A_12))),u1_struct_0(B_20))
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12),u1_struct_0(B_20))))
      | ~ v1_funct_2(D_26,u1_struct_0(A_12),u1_struct_0(B_20))
      | ~ v1_funct_1(D_26)
      | ~ l1_pre_topc(B_20)
      | ~ v2_pre_topc(B_20)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_895,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_840,c_20])).

tff(c_907,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_32,c_55,c_59,c_844,c_510,c_895])).

tff(c_509,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_867,plain,(
    ! [D_138,A_139,B_140] :
      ( v5_pre_topc(D_138,A_139,g1_pre_topc(u1_struct_0(B_140),u1_pre_topc(B_140)))
      | ~ v5_pre_topc(D_138,A_139,B_140)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139),u1_struct_0(g1_pre_topc(u1_struct_0(B_140),u1_pre_topc(B_140))))))
      | ~ v1_funct_2(D_138,u1_struct_0(A_139),u1_struct_0(g1_pre_topc(u1_struct_0(B_140),u1_pre_topc(B_140))))
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(D_138,u1_struct_0(A_139),u1_struct_0(B_140))
      | ~ v1_funct_1(D_138)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_882,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_867])).

tff(c_888,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_32,c_844,c_30,c_882])).

tff(c_889,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_888])).

tff(c_940,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_907,c_889])).

tff(c_941,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_947,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_941])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_947])).

tff(c_954,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_961,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_954])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_961])).

%------------------------------------------------------------------------------
