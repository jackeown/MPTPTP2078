%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 375 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  241 (1240 expanded)
%              Number of equality atoms :   28 ( 160 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_109,plain,(
    ! [A_64,B_65] :
      ( l1_pre_topc(k6_tmap_1(A_64,B_65))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_112,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_109])).

tff(c_115,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_112])).

tff(c_116,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_115])).

tff(c_34,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_57,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_71,plain,(
    ! [A_57,B_58] :
      ( m1_pre_topc(A_57,g1_pre_topc(u1_struct_0(B_58),u1_pre_topc(B_58)))
      | ~ m1_pre_topc(A_57,B_58)
      | ~ l1_pre_topc(B_58)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    ! [A_57] :
      ( m1_pre_topc(A_57,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_57,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_71])).

tff(c_80,plain,(
    ! [A_57] :
      ( m1_pre_topc(A_57,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_57,'#skF_1')
      | ~ l1_pre_topc(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_77])).

tff(c_285,plain,(
    ! [A_83,B_84] :
      ( u1_pre_topc(k6_tmap_1(A_83,B_84)) = k5_tmap_1(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_294,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_285])).

tff(c_300,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_294])).

tff(c_301,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_300])).

tff(c_151,plain,(
    ! [C_71,A_72,B_73] :
      ( m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(u1_struct_0(B_73)))
      | ~ m1_pre_topc(B_73,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [A_74] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_pre_topc('#skF_1',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_177,plain,(
    ! [A_74] :
      ( v3_pre_topc('#skF_2',A_74)
      | ~ r2_hidden('#skF_2',u1_pre_topc(A_74))
      | ~ m1_pre_topc('#skF_1',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_311,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_177])).

tff(c_325,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_311])).

tff(c_434,plain,(
    ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_437,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_434])).

tff(c_440,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_437])).

tff(c_463,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_440])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_463])).

tff(c_469,plain,(
    m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_468,plain,
    ( ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_536,plain,(
    ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_178,plain,(
    ! [A_74] :
      ( r2_hidden('#skF_2',u1_pre_topc(A_74))
      | ~ v3_pre_topc('#skF_2',A_74)
      | ~ m1_pre_topc('#skF_1',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_155,c_4])).

tff(c_308,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_178])).

tff(c_323,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_308])).

tff(c_538,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_323])).

tff(c_539,plain,(
    ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_538])).

tff(c_179,plain,(
    ! [A_75,B_76] :
      ( u1_struct_0(k6_tmap_1(A_75,B_76)) = u1_struct_0(A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_185,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_189,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_185])).

tff(c_190,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_189])).

tff(c_1492,plain,(
    ! [C_134,A_135] :
      ( v3_pre_topc(C_134,k6_tmap_1(A_135,C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_135,C_134))))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1502,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1492])).

tff(c_1509,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_36,c_1502])).

tff(c_1511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_539,c_1509])).

tff(c_1512,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_63,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_2256,plain,(
    ! [D_167,C_168,A_169] :
      ( v3_pre_topc(D_167,C_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0(C_168)))
      | ~ v3_pre_topc(D_167,A_169)
      | ~ m1_pre_topc(C_168,A_169)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2266,plain,(
    ! [A_169] :
      ( v3_pre_topc('#skF_2','#skF_1')
      | ~ v3_pre_topc('#skF_2',A_169)
      | ~ m1_pre_topc('#skF_1',A_169)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_36,c_2256])).

tff(c_2272,plain,(
    ! [A_170] :
      ( ~ v3_pre_topc('#skF_2',A_170)
      | ~ m1_pre_topc('#skF_1',A_170)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_2266])).

tff(c_2281,plain,
    ( ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_2272])).

tff(c_2291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_36,c_469,c_1512,c_2281])).

tff(c_2293,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2292,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2301,plain,(
    ! [B_173,A_174] :
      ( r2_hidden(B_173,u1_pre_topc(A_174))
      | ~ v3_pre_topc(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2304,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2301])).

tff(c_2307,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2292,c_2304])).

tff(c_2982,plain,(
    ! [A_224,B_225] :
      ( k5_tmap_1(A_224,B_225) = u1_pre_topc(A_224)
      | ~ r2_hidden(B_225,u1_pre_topc(A_224))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2997,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2982])).

tff(c_3004,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2307,c_2997])).

tff(c_3005,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3004])).

tff(c_2855,plain,(
    ! [A_218,B_219] :
      ( g1_pre_topc(u1_struct_0(A_218),k5_tmap_1(A_218,B_219)) = k6_tmap_1(A_218,B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2865,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2855])).

tff(c_2872,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2865])).

tff(c_2873,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2872])).

tff(c_3007,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3005,c_2873])).

tff(c_3012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2293,c_3007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.87  
% 4.92/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.87  %$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.92/1.87  
% 4.92/1.87  %Foreground sorts:
% 4.92/1.87  
% 4.92/1.87  
% 4.92/1.87  %Background operators:
% 4.92/1.87  
% 4.92/1.87  
% 4.92/1.87  %Foreground operators:
% 4.92/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.92/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.92/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.92/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.92/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.92/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.92/1.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.92/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.87  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 4.92/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.92/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.92/1.87  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 4.92/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.87  
% 4.92/1.89  tff(f_168, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 4.92/1.89  tff(f_104, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 4.92/1.89  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.92/1.89  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.92/1.89  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 4.92/1.89  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.92/1.89  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.92/1.89  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A, B)))) => ((C = B) => v3_pre_topc(C, k6_tmap_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_tmap_1)).
% 4.92/1.89  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.92/1.89  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 4.92/1.89  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 4.92/1.89  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_109, plain, (![A_64, B_65]: (l1_pre_topc(k6_tmap_1(A_64, B_65)) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.92/1.89  tff(c_112, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_109])).
% 4.92/1.89  tff(c_115, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_112])).
% 4.92/1.89  tff(c_116, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_115])).
% 4.92/1.89  tff(c_34, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.92/1.89  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_57, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 4.92/1.89  tff(c_71, plain, (![A_57, B_58]: (m1_pre_topc(A_57, g1_pre_topc(u1_struct_0(B_58), u1_pre_topc(B_58))) | ~m1_pre_topc(A_57, B_58) | ~l1_pre_topc(B_58) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.92/1.89  tff(c_77, plain, (![A_57]: (m1_pre_topc(A_57, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_57, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_57))), inference(superposition, [status(thm), theory('equality')], [c_57, c_71])).
% 4.92/1.89  tff(c_80, plain, (![A_57]: (m1_pre_topc(A_57, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_57, '#skF_1') | ~l1_pre_topc(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_77])).
% 4.92/1.89  tff(c_285, plain, (![A_83, B_84]: (u1_pre_topc(k6_tmap_1(A_83, B_84))=k5_tmap_1(A_83, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.92/1.89  tff(c_294, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_285])).
% 4.92/1.89  tff(c_300, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_294])).
% 4.92/1.89  tff(c_301, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_300])).
% 4.92/1.89  tff(c_151, plain, (![C_71, A_72, B_73]: (m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(C_71, k1_zfmisc_1(u1_struct_0(B_73))) | ~m1_pre_topc(B_73, A_72) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.92/1.89  tff(c_155, plain, (![A_74]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_pre_topc('#skF_1', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_36, c_151])).
% 4.92/1.89  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.89  tff(c_177, plain, (![A_74]: (v3_pre_topc('#skF_2', A_74) | ~r2_hidden('#skF_2', u1_pre_topc(A_74)) | ~m1_pre_topc('#skF_1', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.92/1.89  tff(c_311, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_177])).
% 4.92/1.89  tff(c_325, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_311])).
% 4.92/1.89  tff(c_434, plain, (~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_325])).
% 4.92/1.89  tff(c_437, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_434])).
% 4.92/1.89  tff(c_440, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_437])).
% 4.92/1.89  tff(c_463, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_440])).
% 4.92/1.89  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_463])).
% 4.92/1.89  tff(c_469, plain, (m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_325])).
% 4.92/1.89  tff(c_468, plain, (~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_325])).
% 4.92/1.89  tff(c_536, plain, (~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_468])).
% 4.92/1.89  tff(c_4, plain, (![B_3, A_1]: (r2_hidden(B_3, u1_pre_topc(A_1)) | ~v3_pre_topc(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.89  tff(c_178, plain, (![A_74]: (r2_hidden('#skF_2', u1_pre_topc(A_74)) | ~v3_pre_topc('#skF_2', A_74) | ~m1_pre_topc('#skF_1', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_155, c_4])).
% 4.92/1.89  tff(c_308, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_301, c_178])).
% 4.92/1.89  tff(c_323, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_308])).
% 4.92/1.89  tff(c_538, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_323])).
% 4.92/1.89  tff(c_539, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_536, c_538])).
% 4.92/1.89  tff(c_179, plain, (![A_75, B_76]: (u1_struct_0(k6_tmap_1(A_75, B_76))=u1_struct_0(A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.92/1.89  tff(c_185, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_179])).
% 4.92/1.89  tff(c_189, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_185])).
% 4.92/1.89  tff(c_190, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_189])).
% 4.92/1.89  tff(c_1492, plain, (![C_134, A_135]: (v3_pre_topc(C_134, k6_tmap_1(A_135, C_134)) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_135, C_134)))) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.92/1.89  tff(c_1502, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_190, c_1492])).
% 4.92/1.89  tff(c_1509, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_36, c_1502])).
% 4.92/1.89  tff(c_1511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_539, c_1509])).
% 4.92/1.89  tff(c_1512, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_468])).
% 4.92/1.89  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_63, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_44])).
% 4.92/1.89  tff(c_2256, plain, (![D_167, C_168, A_169]: (v3_pre_topc(D_167, C_168) | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0(C_168))) | ~v3_pre_topc(D_167, A_169) | ~m1_pre_topc(C_168, A_169) | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.92/1.89  tff(c_2266, plain, (![A_169]: (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', A_169) | ~m1_pre_topc('#skF_1', A_169) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(resolution, [status(thm)], [c_36, c_2256])).
% 4.92/1.89  tff(c_2272, plain, (![A_170]: (~v3_pre_topc('#skF_2', A_170) | ~m1_pre_topc('#skF_1', A_170) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(negUnitSimplification, [status(thm)], [c_63, c_2266])).
% 4.92/1.89  tff(c_2281, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_2272])).
% 4.92/1.89  tff(c_2291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_36, c_469, c_1512, c_2281])).
% 4.92/1.89  tff(c_2293, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.92/1.89  tff(c_2292, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.92/1.89  tff(c_2301, plain, (![B_173, A_174]: (r2_hidden(B_173, u1_pre_topc(A_174)) | ~v3_pre_topc(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.89  tff(c_2304, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2301])).
% 4.92/1.89  tff(c_2307, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2292, c_2304])).
% 4.92/1.89  tff(c_2982, plain, (![A_224, B_225]: (k5_tmap_1(A_224, B_225)=u1_pre_topc(A_224) | ~r2_hidden(B_225, u1_pre_topc(A_224)) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.92/1.89  tff(c_2997, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2982])).
% 4.92/1.89  tff(c_3004, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2307, c_2997])).
% 4.92/1.89  tff(c_3005, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_3004])).
% 4.92/1.89  tff(c_2855, plain, (![A_218, B_219]: (g1_pre_topc(u1_struct_0(A_218), k5_tmap_1(A_218, B_219))=k6_tmap_1(A_218, B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.92/1.89  tff(c_2865, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2855])).
% 4.92/1.89  tff(c_2872, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2865])).
% 4.92/1.89  tff(c_2873, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_2872])).
% 4.92/1.89  tff(c_3007, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3005, c_2873])).
% 4.92/1.89  tff(c_3012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2293, c_3007])).
% 4.92/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.89  
% 4.92/1.89  Inference rules
% 4.92/1.89  ----------------------
% 4.92/1.89  #Ref     : 0
% 4.92/1.89  #Sup     : 566
% 4.92/1.89  #Fact    : 0
% 4.92/1.89  #Define  : 0
% 4.92/1.89  #Split   : 8
% 4.92/1.89  #Chain   : 0
% 4.92/1.89  #Close   : 0
% 4.92/1.89  
% 4.92/1.89  Ordering : KBO
% 4.92/1.89  
% 4.92/1.89  Simplification rules
% 4.92/1.89  ----------------------
% 4.92/1.89  #Subsume      : 71
% 4.92/1.89  #Demod        : 926
% 4.92/1.89  #Tautology    : 263
% 4.92/1.89  #SimpNegUnit  : 81
% 4.92/1.89  #BackRed      : 15
% 4.92/1.89  
% 4.92/1.89  #Partial instantiations: 0
% 4.92/1.89  #Strategies tried      : 1
% 4.92/1.89  
% 4.92/1.89  Timing (in seconds)
% 4.92/1.89  ----------------------
% 4.92/1.90  Preprocessing        : 0.34
% 4.92/1.90  Parsing              : 0.18
% 4.92/1.90  CNF conversion       : 0.02
% 4.92/1.90  Main loop            : 0.78
% 4.92/1.90  Inferencing          : 0.25
% 4.92/1.90  Reduction            : 0.25
% 4.92/1.90  Demodulation         : 0.18
% 4.92/1.90  BG Simplification    : 0.03
% 4.92/1.90  Subsumption          : 0.19
% 4.92/1.90  Abstraction          : 0.04
% 4.92/1.90  MUC search           : 0.00
% 4.92/1.90  Cooper               : 0.00
% 4.92/1.90  Total                : 1.17
% 4.92/1.90  Index Insertion      : 0.00
% 4.92/1.90  Index Deletion       : 0.00
% 4.92/1.90  Index Matching       : 0.00
% 4.92/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
