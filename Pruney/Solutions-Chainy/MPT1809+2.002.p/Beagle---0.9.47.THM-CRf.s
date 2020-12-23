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
% DateTime   : Thu Dec  3 10:28:04 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 479 expanded)
%              Number of leaves         :   38 ( 205 expanded)
%              Depth                    :   12
%              Number of atoms          :  576 (4222 expanded)
%              Number of equality atoms :   44 ( 553 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( A = k1_tsep_1(A,D,E)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(A))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(E))
                                     => ( ( F = G
                                          & F = H )
                                       => ( r1_tmap_1(A,B,C,F)
                                        <=> ( r1_tmap_1(D,B,k2_tmap_1(A,B,C,D),G)
                                            & r1_tmap_1(E,B,k2_tmap_1(A,B,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(k1_tsep_1(A,D,E)))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ! [H] :
                                  ( m1_subset_1(H,u1_struct_0(E))
                                 => ( ( F = G
                                      & F = H )
                                   => ( r1_tmap_1(k1_tsep_1(A,D,E),B,k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)),F)
                                    <=> ( r1_tmap_1(D,B,k2_tmap_1(A,B,C,D),G)
                                        & r1_tmap_1(E,B,k2_tmap_1(A,B,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).

tff(c_26,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_28,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_77])).

tff(c_123,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_70])).

tff(c_96,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_75,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_64])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_75])).

tff(c_161,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_96,c_81])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_36,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_153,plain,(
    ! [A_555,B_556,C_557] :
      ( m1_pre_topc(k1_tsep_1(A_555,B_556,C_557),A_555)
      | ~ m1_pre_topc(C_557,A_555)
      | v2_struct_0(C_557)
      | ~ m1_pre_topc(B_556,A_555)
      | v2_struct_0(B_556)
      | ~ l1_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_156,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_153])).

tff(c_158,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42,c_38,c_156])).

tff(c_159,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44,c_40,c_158])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_124,plain,(
    ! [A_544,B_545,C_546,D_547] :
      ( k2_partfun1(A_544,B_545,C_546,D_547) = k7_relat_1(C_546,D_547)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545)))
      | ~ v1_funct_1(C_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    ! [D_547] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_547) = k7_relat_1('#skF_3',D_547)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_124])).

tff(c_129,plain,(
    ! [D_547] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_547) = k7_relat_1('#skF_3',D_547) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_126])).

tff(c_162,plain,(
    ! [A_558,B_559,C_560,D_561] :
      ( k2_partfun1(u1_struct_0(A_558),u1_struct_0(B_559),C_560,u1_struct_0(D_561)) = k2_tmap_1(A_558,B_559,C_560,D_561)
      | ~ m1_pre_topc(D_561,A_558)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_558),u1_struct_0(B_559))))
      | ~ v1_funct_2(C_560,u1_struct_0(A_558),u1_struct_0(B_559))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc(B_559)
      | ~ v2_pre_topc(B_559)
      | v2_struct_0(B_559)
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558)
      | v2_struct_0(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_164,plain,(
    ! [D_561] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_561)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561)
      | ~ m1_pre_topc(D_561,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_162])).

tff(c_167,plain,(
    ! [D_561] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_561)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_561)
      | ~ m1_pre_topc(D_561,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_129,c_164])).

tff(c_169,plain,(
    ! [D_562] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_562)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_562)
      | ~ m1_pre_topc(D_562,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_167])).

tff(c_97,plain,(
    ! [C_533,A_534,B_535] :
      ( v1_relat_1(C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_534,B_535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_97])).

tff(c_102,plain,(
    ! [C_536,A_537,B_538] :
      ( v4_relat_1(C_536,A_537)
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_107,plain,(
    ! [B_539,A_540] :
      ( k7_relat_1(B_539,A_540) = B_539
      | ~ v4_relat_1(B_539,A_540)
      | ~ v1_relat_1(B_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_107])).

tff(c_113,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_110])).

tff(c_175,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_113])).

tff(c_184,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_175])).

tff(c_230,plain,(
    ! [H_588,C_583,A_585,D_587,B_586,E_584] :
      ( r1_tmap_1(k1_tsep_1(A_585,D_587,E_584),B_586,k2_tmap_1(A_585,B_586,C_583,k1_tsep_1(A_585,D_587,E_584)),H_588)
      | ~ r1_tmap_1(E_584,B_586,k2_tmap_1(A_585,B_586,C_583,E_584),H_588)
      | ~ r1_tmap_1(D_587,B_586,k2_tmap_1(A_585,B_586,C_583,D_587),H_588)
      | ~ m1_subset_1(H_588,u1_struct_0(E_584))
      | ~ m1_subset_1(H_588,u1_struct_0(D_587))
      | ~ m1_subset_1(H_588,u1_struct_0(k1_tsep_1(A_585,D_587,E_584)))
      | ~ m1_pre_topc(E_584,A_585)
      | v2_struct_0(E_584)
      | ~ m1_pre_topc(D_587,A_585)
      | v2_struct_0(D_587)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_585),u1_struct_0(B_586))))
      | ~ v1_funct_2(C_583,u1_struct_0(A_585),u1_struct_0(B_586))
      | ~ v1_funct_1(C_583)
      | ~ l1_pre_topc(B_586)
      | ~ v2_pre_topc(B_586)
      | v2_struct_0(B_586)
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_232,plain,(
    ! [D_587,E_584,H_588] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_587,E_584),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_587,E_584)),H_588)
      | ~ r1_tmap_1(E_584,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_584),H_588)
      | ~ r1_tmap_1(D_587,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_587),H_588)
      | ~ m1_subset_1(H_588,u1_struct_0(E_584))
      | ~ m1_subset_1(H_588,u1_struct_0(D_587))
      | ~ m1_subset_1(H_588,u1_struct_0(k1_tsep_1('#skF_1',D_587,E_584)))
      | ~ m1_pre_topc(E_584,'#skF_1')
      | v2_struct_0(E_584)
      | ~ m1_pre_topc(D_587,'#skF_1')
      | v2_struct_0(D_587)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_230])).

tff(c_235,plain,(
    ! [D_587,E_584,H_588] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_587,E_584),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_587,E_584)),H_588)
      | ~ r1_tmap_1(E_584,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_584),H_588)
      | ~ r1_tmap_1(D_587,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_587),H_588)
      | ~ m1_subset_1(H_588,u1_struct_0(E_584))
      | ~ m1_subset_1(H_588,u1_struct_0(D_587))
      | ~ m1_subset_1(H_588,u1_struct_0(k1_tsep_1('#skF_1',D_587,E_584)))
      | ~ m1_pre_topc(E_584,'#skF_1')
      | v2_struct_0(E_584)
      | ~ m1_pre_topc(D_587,'#skF_1')
      | v2_struct_0(D_587)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_232])).

tff(c_237,plain,(
    ! [D_589,E_590,H_591] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_589,E_590),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_589,E_590)),H_591)
      | ~ r1_tmap_1(E_590,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_590),H_591)
      | ~ r1_tmap_1(D_589,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_589),H_591)
      | ~ m1_subset_1(H_591,u1_struct_0(E_590))
      | ~ m1_subset_1(H_591,u1_struct_0(D_589))
      | ~ m1_subset_1(H_591,u1_struct_0(k1_tsep_1('#skF_1',D_589,E_590)))
      | ~ m1_pre_topc(E_590,'#skF_1')
      | v2_struct_0(E_590)
      | ~ m1_pre_topc(D_589,'#skF_1')
      | v2_struct_0(D_589) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_235])).

tff(c_244,plain,(
    ! [H_591] :
      ( r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_591)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_591)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_591)
      | ~ m1_subset_1(H_591,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_591,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_591,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_237])).

tff(c_257,plain,(
    ! [H_591] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_591)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_591)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_591)
      | ~ m1_subset_1(H_591,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_591,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_591,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_184,c_36,c_244])).

tff(c_262,plain,(
    ! [H_592] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_592)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_592)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_592)
      | ~ m1_subset_1(H_592,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_592,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_592,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_257])).

tff(c_268,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_96,c_262])).

tff(c_272,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_82,c_30,c_123,c_268])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_272])).

tff(c_275,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_306,plain,(
    ! [A_604,B_605,C_606] :
      ( m1_pre_topc(k1_tsep_1(A_604,B_605,C_606),A_604)
      | ~ m1_pre_topc(C_606,A_604)
      | v2_struct_0(C_606)
      | ~ m1_pre_topc(B_605,A_604)
      | v2_struct_0(B_605)
      | ~ l1_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_309,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_306])).

tff(c_311,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42,c_38,c_309])).

tff(c_312,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44,c_40,c_311])).

tff(c_277,plain,(
    ! [A_593,B_594,C_595,D_596] :
      ( k2_partfun1(A_593,B_594,C_595,D_596) = k7_relat_1(C_595,D_596)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | ~ v1_funct_1(C_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_279,plain,(
    ! [D_596] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_596) = k7_relat_1('#skF_3',D_596)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_277])).

tff(c_282,plain,(
    ! [D_596] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_596) = k7_relat_1('#skF_3',D_596) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_279])).

tff(c_315,plain,(
    ! [A_607,B_608,C_609,D_610] :
      ( k2_partfun1(u1_struct_0(A_607),u1_struct_0(B_608),C_609,u1_struct_0(D_610)) = k2_tmap_1(A_607,B_608,C_609,D_610)
      | ~ m1_pre_topc(D_610,A_607)
      | ~ m1_subset_1(C_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_607),u1_struct_0(B_608))))
      | ~ v1_funct_2(C_609,u1_struct_0(A_607),u1_struct_0(B_608))
      | ~ v1_funct_1(C_609)
      | ~ l1_pre_topc(B_608)
      | ~ v2_pre_topc(B_608)
      | v2_struct_0(B_608)
      | ~ l1_pre_topc(A_607)
      | ~ v2_pre_topc(A_607)
      | v2_struct_0(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_317,plain,(
    ! [D_610] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_610)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_610)
      | ~ m1_pre_topc(D_610,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_315])).

tff(c_320,plain,(
    ! [D_610] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_610)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_610)
      | ~ m1_pre_topc(D_610,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_282,c_317])).

tff(c_333,plain,(
    ! [D_617] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_617)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_617)
      | ~ m1_pre_topc(D_617,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_320])).

tff(c_339,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_113])).

tff(c_348,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_339])).

tff(c_322,plain,(
    ! [C_611,D_615,H_616,B_614,A_613,E_612] :
      ( r1_tmap_1(D_615,B_614,k2_tmap_1(A_613,B_614,C_611,D_615),H_616)
      | ~ r1_tmap_1(k1_tsep_1(A_613,D_615,E_612),B_614,k2_tmap_1(A_613,B_614,C_611,k1_tsep_1(A_613,D_615,E_612)),H_616)
      | ~ m1_subset_1(H_616,u1_struct_0(E_612))
      | ~ m1_subset_1(H_616,u1_struct_0(D_615))
      | ~ m1_subset_1(H_616,u1_struct_0(k1_tsep_1(A_613,D_615,E_612)))
      | ~ m1_pre_topc(E_612,A_613)
      | v2_struct_0(E_612)
      | ~ m1_pre_topc(D_615,A_613)
      | v2_struct_0(D_615)
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613),u1_struct_0(B_614))))
      | ~ v1_funct_2(C_611,u1_struct_0(A_613),u1_struct_0(B_614))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_614)
      | ~ v2_pre_topc(B_614)
      | v2_struct_0(B_614)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_324,plain,(
    ! [B_614,C_611,H_616] :
      ( r1_tmap_1('#skF_4',B_614,k2_tmap_1('#skF_1',B_614,C_611,'#skF_4'),H_616)
      | ~ r1_tmap_1('#skF_1',B_614,k2_tmap_1('#skF_1',B_614,C_611,k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_616)
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_616,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_614))))
      | ~ v1_funct_2(C_611,u1_struct_0('#skF_1'),u1_struct_0(B_614))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_614)
      | ~ v2_pre_topc(B_614)
      | v2_struct_0(B_614)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_322])).

tff(c_328,plain,(
    ! [B_614,C_611,H_616] :
      ( r1_tmap_1('#skF_4',B_614,k2_tmap_1('#skF_1',B_614,C_611,'#skF_4'),H_616)
      | ~ r1_tmap_1('#skF_1',B_614,k2_tmap_1('#skF_1',B_614,C_611,'#skF_1'),H_616)
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_614))))
      | ~ v1_funct_2(C_611,u1_struct_0('#skF_1'),u1_struct_0(B_614))
      | ~ v1_funct_1(C_611)
      | ~ l1_pre_topc(B_614)
      | ~ v2_pre_topc(B_614)
      | v2_struct_0(B_614)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_38,c_36,c_36,c_324])).

tff(c_357,plain,(
    ! [B_618,C_619,H_620] :
      ( r1_tmap_1('#skF_4',B_618,k2_tmap_1('#skF_1',B_618,C_619,'#skF_4'),H_620)
      | ~ r1_tmap_1('#skF_1',B_618,k2_tmap_1('#skF_1',B_618,C_619,'#skF_1'),H_620)
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_619,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_618))))
      | ~ v1_funct_2(C_619,u1_struct_0('#skF_1'),u1_struct_0(B_618))
      | ~ v1_funct_1(C_619)
      | ~ l1_pre_topc(B_618)
      | ~ v2_pre_topc(B_618)
      | v2_struct_0(B_618) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44,c_40,c_328])).

tff(c_359,plain,(
    ! [H_620] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_620)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_620)
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_357])).

tff(c_361,plain,(
    ! [H_620] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_620)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_620)
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_620,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_359])).

tff(c_363,plain,(
    ! [H_621] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_621)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_621)
      | ~ m1_subset_1(H_621,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_621,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_621,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_361])).

tff(c_276,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_366,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_363,c_276])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_82,c_30,c_275,c_366])).

tff(c_371,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_429,plain,(
    ! [A_644,B_645,C_646] :
      ( m1_pre_topc(k1_tsep_1(A_644,B_645,C_646),A_644)
      | ~ m1_pre_topc(C_646,A_644)
      | v2_struct_0(C_646)
      | ~ m1_pre_topc(B_645,A_644)
      | v2_struct_0(B_645)
      | ~ l1_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_432,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_429])).

tff(c_434,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42,c_38,c_432])).

tff(c_435,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44,c_40,c_434])).

tff(c_400,plain,(
    ! [A_633,B_634,C_635,D_636] :
      ( k2_partfun1(A_633,B_634,C_635,D_636) = k7_relat_1(C_635,D_636)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634)))
      | ~ v1_funct_1(C_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    ! [D_636] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_636) = k7_relat_1('#skF_3',D_636)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_400])).

tff(c_405,plain,(
    ! [D_636] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_636) = k7_relat_1('#skF_3',D_636) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_402])).

tff(c_438,plain,(
    ! [A_647,B_648,C_649,D_650] :
      ( k2_partfun1(u1_struct_0(A_647),u1_struct_0(B_648),C_649,u1_struct_0(D_650)) = k2_tmap_1(A_647,B_648,C_649,D_650)
      | ~ m1_pre_topc(D_650,A_647)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647),u1_struct_0(B_648))))
      | ~ v1_funct_2(C_649,u1_struct_0(A_647),u1_struct_0(B_648))
      | ~ v1_funct_1(C_649)
      | ~ l1_pre_topc(B_648)
      | ~ v2_pre_topc(B_648)
      | v2_struct_0(B_648)
      | ~ l1_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_440,plain,(
    ! [D_650] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_650)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_650)
      | ~ m1_pre_topc(D_650,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_438])).

tff(c_443,plain,(
    ! [D_650] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_650)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_650)
      | ~ m1_pre_topc(D_650,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_48,c_405,c_440])).

tff(c_445,plain,(
    ! [D_651] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_651)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_651)
      | ~ m1_pre_topc(D_651,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_443])).

tff(c_373,plain,(
    ! [C_622,A_623,B_624] :
      ( v1_relat_1(C_622)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_623,B_624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_377,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_373])).

tff(c_384,plain,(
    ! [C_630,A_631,B_632] :
      ( v4_relat_1(C_630,A_631)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_384])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_391,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_394,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_391])).

tff(c_451,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_394])).

tff(c_460,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_451])).

tff(c_480,plain,(
    ! [E_659,C_658,D_662,B_661,A_660,H_663] :
      ( r1_tmap_1(E_659,B_661,k2_tmap_1(A_660,B_661,C_658,E_659),H_663)
      | ~ r1_tmap_1(k1_tsep_1(A_660,D_662,E_659),B_661,k2_tmap_1(A_660,B_661,C_658,k1_tsep_1(A_660,D_662,E_659)),H_663)
      | ~ m1_subset_1(H_663,u1_struct_0(E_659))
      | ~ m1_subset_1(H_663,u1_struct_0(D_662))
      | ~ m1_subset_1(H_663,u1_struct_0(k1_tsep_1(A_660,D_662,E_659)))
      | ~ m1_pre_topc(E_659,A_660)
      | v2_struct_0(E_659)
      | ~ m1_pre_topc(D_662,A_660)
      | v2_struct_0(D_662)
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660),u1_struct_0(B_661))))
      | ~ v1_funct_2(C_658,u1_struct_0(A_660),u1_struct_0(B_661))
      | ~ v1_funct_1(C_658)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc(A_660)
      | ~ v2_pre_topc(A_660)
      | v2_struct_0(A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_482,plain,(
    ! [B_661,C_658,H_663] :
      ( r1_tmap_1('#skF_5',B_661,k2_tmap_1('#skF_1',B_661,C_658,'#skF_5'),H_663)
      | ~ r1_tmap_1('#skF_1',B_661,k2_tmap_1('#skF_1',B_661,C_658,k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_663)
      | ~ m1_subset_1(H_663,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_663,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_663,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_661))))
      | ~ v1_funct_2(C_658,u1_struct_0('#skF_1'),u1_struct_0(B_661))
      | ~ v1_funct_1(C_658)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_480])).

tff(c_486,plain,(
    ! [B_661,C_658,H_663] :
      ( r1_tmap_1('#skF_5',B_661,k2_tmap_1('#skF_1',B_661,C_658,'#skF_5'),H_663)
      | ~ r1_tmap_1('#skF_1',B_661,k2_tmap_1('#skF_1',B_661,C_658,'#skF_1'),H_663)
      | ~ m1_subset_1(H_663,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_663,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_663,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_661))))
      | ~ v1_funct_2(C_658,u1_struct_0('#skF_1'),u1_struct_0(B_661))
      | ~ v1_funct_1(C_658)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_38,c_36,c_36,c_482])).

tff(c_498,plain,(
    ! [B_668,C_669,H_670] :
      ( r1_tmap_1('#skF_5',B_668,k2_tmap_1('#skF_1',B_668,C_669,'#skF_5'),H_670)
      | ~ r1_tmap_1('#skF_1',B_668,k2_tmap_1('#skF_1',B_668,C_669,'#skF_1'),H_670)
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_669,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_668))))
      | ~ v1_funct_2(C_669,u1_struct_0('#skF_1'),u1_struct_0(B_668))
      | ~ v1_funct_1(C_669)
      | ~ l1_pre_topc(B_668)
      | ~ v2_pre_topc(B_668)
      | v2_struct_0(B_668) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_44,c_40,c_486])).

tff(c_500,plain,(
    ! [H_670] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_670)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_670)
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_498])).

tff(c_503,plain,(
    ! [H_670] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_670)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_670)
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_670,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_460,c_500])).

tff(c_505,plain,(
    ! [H_671] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_671)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_671)
      | ~ m1_subset_1(H_671,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_671,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_671,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_503])).

tff(c_372,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_508,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_505,c_372])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_82,c_30,c_371,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:37:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  %$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.33/1.54  
% 3.33/1.54  %Foreground sorts:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Background operators:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Foreground operators:
% 3.33/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.54  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.33/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.33/1.54  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.33/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.54  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.33/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.54  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.33/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.54  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.33/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.54  
% 3.33/1.57  tff(f_205, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 3.33/1.57  tff(f_96, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.33/1.57  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.33/1.57  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.33/1.57  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.57  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.57  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.33/1.57  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (![F]: (m1_subset_1(F, u1_struct_0(k1_tsep_1(A, D, E))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(k1_tsep_1(A, D, E), B, k2_tmap_1(A, B, C, k1_tsep_1(A, D, E)), F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 3.33/1.57  tff(c_26, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34])).
% 3.33/1.57  tff(c_28, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_32, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_76, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.33/1.57  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_76])).
% 3.33/1.57  tff(c_30, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_74, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_77, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74])).
% 3.33/1.57  tff(c_83, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_77])).
% 3.33/1.57  tff(c_123, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 3.33/1.57  tff(c_70, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_78, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_70])).
% 3.33/1.57  tff(c_96, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 3.33/1.57  tff(c_64, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_75, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_64])).
% 3.33/1.57  tff(c_81, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_75])).
% 3.33/1.57  tff(c_161, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_96, c_81])).
% 3.33/1.57  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_36, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_153, plain, (![A_555, B_556, C_557]: (m1_pre_topc(k1_tsep_1(A_555, B_556, C_557), A_555) | ~m1_pre_topc(C_557, A_555) | v2_struct_0(C_557) | ~m1_pre_topc(B_556, A_555) | v2_struct_0(B_556) | ~l1_pre_topc(A_555) | v2_struct_0(A_555))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.33/1.57  tff(c_156, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_153])).
% 3.33/1.57  tff(c_158, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_42, c_38, c_156])).
% 3.33/1.57  tff(c_159, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_44, c_40, c_158])).
% 3.33/1.57  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.33/1.57  tff(c_124, plain, (![A_544, B_545, C_546, D_547]: (k2_partfun1(A_544, B_545, C_546, D_547)=k7_relat_1(C_546, D_547) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))) | ~v1_funct_1(C_546))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.57  tff(c_126, plain, (![D_547]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_547)=k7_relat_1('#skF_3', D_547) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_124])).
% 3.33/1.57  tff(c_129, plain, (![D_547]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_547)=k7_relat_1('#skF_3', D_547))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_126])).
% 3.33/1.57  tff(c_162, plain, (![A_558, B_559, C_560, D_561]: (k2_partfun1(u1_struct_0(A_558), u1_struct_0(B_559), C_560, u1_struct_0(D_561))=k2_tmap_1(A_558, B_559, C_560, D_561) | ~m1_pre_topc(D_561, A_558) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_558), u1_struct_0(B_559)))) | ~v1_funct_2(C_560, u1_struct_0(A_558), u1_struct_0(B_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc(B_559) | ~v2_pre_topc(B_559) | v2_struct_0(B_559) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558) | v2_struct_0(A_558))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.57  tff(c_164, plain, (![D_561]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_561))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561) | ~m1_pre_topc(D_561, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_162])).
% 3.33/1.57  tff(c_167, plain, (![D_561]: (k7_relat_1('#skF_3', u1_struct_0(D_561))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_561) | ~m1_pre_topc(D_561, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_129, c_164])).
% 3.33/1.57  tff(c_169, plain, (![D_562]: (k7_relat_1('#skF_3', u1_struct_0(D_562))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_562) | ~m1_pre_topc(D_562, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_167])).
% 3.33/1.57  tff(c_97, plain, (![C_533, A_534, B_535]: (v1_relat_1(C_533) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_534, B_535))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.57  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_97])).
% 3.33/1.57  tff(c_102, plain, (![C_536, A_537, B_538]: (v4_relat_1(C_536, A_537) | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.57  tff(c_106, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_102])).
% 3.33/1.57  tff(c_107, plain, (![B_539, A_540]: (k7_relat_1(B_539, A_540)=B_539 | ~v4_relat_1(B_539, A_540) | ~v1_relat_1(B_539))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.57  tff(c_110, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_107])).
% 3.33/1.57  tff(c_113, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_110])).
% 3.33/1.57  tff(c_175, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_169, c_113])).
% 3.33/1.57  tff(c_184, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_175])).
% 3.33/1.57  tff(c_230, plain, (![H_588, C_583, A_585, D_587, B_586, E_584]: (r1_tmap_1(k1_tsep_1(A_585, D_587, E_584), B_586, k2_tmap_1(A_585, B_586, C_583, k1_tsep_1(A_585, D_587, E_584)), H_588) | ~r1_tmap_1(E_584, B_586, k2_tmap_1(A_585, B_586, C_583, E_584), H_588) | ~r1_tmap_1(D_587, B_586, k2_tmap_1(A_585, B_586, C_583, D_587), H_588) | ~m1_subset_1(H_588, u1_struct_0(E_584)) | ~m1_subset_1(H_588, u1_struct_0(D_587)) | ~m1_subset_1(H_588, u1_struct_0(k1_tsep_1(A_585, D_587, E_584))) | ~m1_pre_topc(E_584, A_585) | v2_struct_0(E_584) | ~m1_pre_topc(D_587, A_585) | v2_struct_0(D_587) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_585), u1_struct_0(B_586)))) | ~v1_funct_2(C_583, u1_struct_0(A_585), u1_struct_0(B_586)) | ~v1_funct_1(C_583) | ~l1_pre_topc(B_586) | ~v2_pre_topc(B_586) | v2_struct_0(B_586) | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.33/1.57  tff(c_232, plain, (![D_587, E_584, H_588]: (r1_tmap_1(k1_tsep_1('#skF_1', D_587, E_584), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_587, E_584)), H_588) | ~r1_tmap_1(E_584, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_584), H_588) | ~r1_tmap_1(D_587, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_587), H_588) | ~m1_subset_1(H_588, u1_struct_0(E_584)) | ~m1_subset_1(H_588, u1_struct_0(D_587)) | ~m1_subset_1(H_588, u1_struct_0(k1_tsep_1('#skF_1', D_587, E_584))) | ~m1_pre_topc(E_584, '#skF_1') | v2_struct_0(E_584) | ~m1_pre_topc(D_587, '#skF_1') | v2_struct_0(D_587) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_230])).
% 3.33/1.57  tff(c_235, plain, (![D_587, E_584, H_588]: (r1_tmap_1(k1_tsep_1('#skF_1', D_587, E_584), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_587, E_584)), H_588) | ~r1_tmap_1(E_584, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_584), H_588) | ~r1_tmap_1(D_587, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_587), H_588) | ~m1_subset_1(H_588, u1_struct_0(E_584)) | ~m1_subset_1(H_588, u1_struct_0(D_587)) | ~m1_subset_1(H_588, u1_struct_0(k1_tsep_1('#skF_1', D_587, E_584))) | ~m1_pre_topc(E_584, '#skF_1') | v2_struct_0(E_584) | ~m1_pre_topc(D_587, '#skF_1') | v2_struct_0(D_587) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_232])).
% 3.33/1.57  tff(c_237, plain, (![D_589, E_590, H_591]: (r1_tmap_1(k1_tsep_1('#skF_1', D_589, E_590), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_589, E_590)), H_591) | ~r1_tmap_1(E_590, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_590), H_591) | ~r1_tmap_1(D_589, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_589), H_591) | ~m1_subset_1(H_591, u1_struct_0(E_590)) | ~m1_subset_1(H_591, u1_struct_0(D_589)) | ~m1_subset_1(H_591, u1_struct_0(k1_tsep_1('#skF_1', D_589, E_590))) | ~m1_pre_topc(E_590, '#skF_1') | v2_struct_0(E_590) | ~m1_pre_topc(D_589, '#skF_1') | v2_struct_0(D_589))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_235])).
% 3.33/1.57  tff(c_244, plain, (![H_591]: (r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_591) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_591) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_591) | ~m1_subset_1(H_591, u1_struct_0('#skF_5')) | ~m1_subset_1(H_591, u1_struct_0('#skF_4')) | ~m1_subset_1(H_591, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_237])).
% 3.33/1.57  tff(c_257, plain, (![H_591]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_591) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_591) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_591) | ~m1_subset_1(H_591, u1_struct_0('#skF_5')) | ~m1_subset_1(H_591, u1_struct_0('#skF_4')) | ~m1_subset_1(H_591, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_184, c_36, c_244])).
% 3.33/1.57  tff(c_262, plain, (![H_592]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_592) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_592) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_592) | ~m1_subset_1(H_592, u1_struct_0('#skF_5')) | ~m1_subset_1(H_592, u1_struct_0('#skF_4')) | ~m1_subset_1(H_592, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_257])).
% 3.33/1.57  tff(c_268, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_96, c_262])).
% 3.33/1.57  tff(c_272, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_82, c_30, c_123, c_268])).
% 3.33/1.57  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_272])).
% 3.33/1.57  tff(c_275, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 3.33/1.57  tff(c_306, plain, (![A_604, B_605, C_606]: (m1_pre_topc(k1_tsep_1(A_604, B_605, C_606), A_604) | ~m1_pre_topc(C_606, A_604) | v2_struct_0(C_606) | ~m1_pre_topc(B_605, A_604) | v2_struct_0(B_605) | ~l1_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.33/1.57  tff(c_309, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_306])).
% 3.33/1.57  tff(c_311, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_42, c_38, c_309])).
% 3.33/1.57  tff(c_312, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_44, c_40, c_311])).
% 3.33/1.57  tff(c_277, plain, (![A_593, B_594, C_595, D_596]: (k2_partfun1(A_593, B_594, C_595, D_596)=k7_relat_1(C_595, D_596) | ~m1_subset_1(C_595, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | ~v1_funct_1(C_595))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.57  tff(c_279, plain, (![D_596]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_596)=k7_relat_1('#skF_3', D_596) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_277])).
% 3.33/1.57  tff(c_282, plain, (![D_596]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_596)=k7_relat_1('#skF_3', D_596))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_279])).
% 3.33/1.57  tff(c_315, plain, (![A_607, B_608, C_609, D_610]: (k2_partfun1(u1_struct_0(A_607), u1_struct_0(B_608), C_609, u1_struct_0(D_610))=k2_tmap_1(A_607, B_608, C_609, D_610) | ~m1_pre_topc(D_610, A_607) | ~m1_subset_1(C_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_607), u1_struct_0(B_608)))) | ~v1_funct_2(C_609, u1_struct_0(A_607), u1_struct_0(B_608)) | ~v1_funct_1(C_609) | ~l1_pre_topc(B_608) | ~v2_pre_topc(B_608) | v2_struct_0(B_608) | ~l1_pre_topc(A_607) | ~v2_pre_topc(A_607) | v2_struct_0(A_607))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.57  tff(c_317, plain, (![D_610]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_610))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_610) | ~m1_pre_topc(D_610, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_315])).
% 3.33/1.57  tff(c_320, plain, (![D_610]: (k7_relat_1('#skF_3', u1_struct_0(D_610))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_610) | ~m1_pre_topc(D_610, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_282, c_317])).
% 3.33/1.57  tff(c_333, plain, (![D_617]: (k7_relat_1('#skF_3', u1_struct_0(D_617))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_617) | ~m1_pre_topc(D_617, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_320])).
% 3.33/1.57  tff(c_339, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_333, c_113])).
% 3.33/1.57  tff(c_348, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_339])).
% 3.33/1.57  tff(c_322, plain, (![C_611, D_615, H_616, B_614, A_613, E_612]: (r1_tmap_1(D_615, B_614, k2_tmap_1(A_613, B_614, C_611, D_615), H_616) | ~r1_tmap_1(k1_tsep_1(A_613, D_615, E_612), B_614, k2_tmap_1(A_613, B_614, C_611, k1_tsep_1(A_613, D_615, E_612)), H_616) | ~m1_subset_1(H_616, u1_struct_0(E_612)) | ~m1_subset_1(H_616, u1_struct_0(D_615)) | ~m1_subset_1(H_616, u1_struct_0(k1_tsep_1(A_613, D_615, E_612))) | ~m1_pre_topc(E_612, A_613) | v2_struct_0(E_612) | ~m1_pre_topc(D_615, A_613) | v2_struct_0(D_615) | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613), u1_struct_0(B_614)))) | ~v1_funct_2(C_611, u1_struct_0(A_613), u1_struct_0(B_614)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_614) | ~v2_pre_topc(B_614) | v2_struct_0(B_614) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.33/1.57  tff(c_324, plain, (![B_614, C_611, H_616]: (r1_tmap_1('#skF_4', B_614, k2_tmap_1('#skF_1', B_614, C_611, '#skF_4'), H_616) | ~r1_tmap_1('#skF_1', B_614, k2_tmap_1('#skF_1', B_614, C_611, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_616) | ~m1_subset_1(H_616, u1_struct_0('#skF_5')) | ~m1_subset_1(H_616, u1_struct_0('#skF_4')) | ~m1_subset_1(H_616, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_614)))) | ~v1_funct_2(C_611, u1_struct_0('#skF_1'), u1_struct_0(B_614)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_614) | ~v2_pre_topc(B_614) | v2_struct_0(B_614) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_322])).
% 3.33/1.57  tff(c_328, plain, (![B_614, C_611, H_616]: (r1_tmap_1('#skF_4', B_614, k2_tmap_1('#skF_1', B_614, C_611, '#skF_4'), H_616) | ~r1_tmap_1('#skF_1', B_614, k2_tmap_1('#skF_1', B_614, C_611, '#skF_1'), H_616) | ~m1_subset_1(H_616, u1_struct_0('#skF_5')) | ~m1_subset_1(H_616, u1_struct_0('#skF_4')) | ~m1_subset_1(H_616, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_614)))) | ~v1_funct_2(C_611, u1_struct_0('#skF_1'), u1_struct_0(B_614)) | ~v1_funct_1(C_611) | ~l1_pre_topc(B_614) | ~v2_pre_topc(B_614) | v2_struct_0(B_614) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_38, c_36, c_36, c_324])).
% 3.33/1.57  tff(c_357, plain, (![B_618, C_619, H_620]: (r1_tmap_1('#skF_4', B_618, k2_tmap_1('#skF_1', B_618, C_619, '#skF_4'), H_620) | ~r1_tmap_1('#skF_1', B_618, k2_tmap_1('#skF_1', B_618, C_619, '#skF_1'), H_620) | ~m1_subset_1(H_620, u1_struct_0('#skF_5')) | ~m1_subset_1(H_620, u1_struct_0('#skF_4')) | ~m1_subset_1(H_620, u1_struct_0('#skF_1')) | ~m1_subset_1(C_619, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_618)))) | ~v1_funct_2(C_619, u1_struct_0('#skF_1'), u1_struct_0(B_618)) | ~v1_funct_1(C_619) | ~l1_pre_topc(B_618) | ~v2_pre_topc(B_618) | v2_struct_0(B_618))), inference(negUnitSimplification, [status(thm)], [c_62, c_44, c_40, c_328])).
% 3.33/1.57  tff(c_359, plain, (![H_620]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_620) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_620) | ~m1_subset_1(H_620, u1_struct_0('#skF_5')) | ~m1_subset_1(H_620, u1_struct_0('#skF_4')) | ~m1_subset_1(H_620, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_357])).
% 3.33/1.57  tff(c_361, plain, (![H_620]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_620) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_620) | ~m1_subset_1(H_620, u1_struct_0('#skF_5')) | ~m1_subset_1(H_620, u1_struct_0('#skF_4')) | ~m1_subset_1(H_620, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_46, c_359])).
% 3.33/1.57  tff(c_363, plain, (![H_621]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_621) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_621) | ~m1_subset_1(H_621, u1_struct_0('#skF_5')) | ~m1_subset_1(H_621, u1_struct_0('#skF_4')) | ~m1_subset_1(H_621, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_361])).
% 3.33/1.57  tff(c_276, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 3.33/1.57  tff(c_366, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_363, c_276])).
% 3.33/1.57  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_82, c_30, c_275, c_366])).
% 3.33/1.57  tff(c_371, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.33/1.57  tff(c_429, plain, (![A_644, B_645, C_646]: (m1_pre_topc(k1_tsep_1(A_644, B_645, C_646), A_644) | ~m1_pre_topc(C_646, A_644) | v2_struct_0(C_646) | ~m1_pre_topc(B_645, A_644) | v2_struct_0(B_645) | ~l1_pre_topc(A_644) | v2_struct_0(A_644))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.33/1.57  tff(c_432, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36, c_429])).
% 3.33/1.57  tff(c_434, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_42, c_38, c_432])).
% 3.33/1.57  tff(c_435, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_44, c_40, c_434])).
% 3.33/1.57  tff(c_400, plain, (![A_633, B_634, C_635, D_636]: (k2_partfun1(A_633, B_634, C_635, D_636)=k7_relat_1(C_635, D_636) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))) | ~v1_funct_1(C_635))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.57  tff(c_402, plain, (![D_636]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_636)=k7_relat_1('#skF_3', D_636) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_400])).
% 3.33/1.57  tff(c_405, plain, (![D_636]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_636)=k7_relat_1('#skF_3', D_636))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_402])).
% 3.33/1.57  tff(c_438, plain, (![A_647, B_648, C_649, D_650]: (k2_partfun1(u1_struct_0(A_647), u1_struct_0(B_648), C_649, u1_struct_0(D_650))=k2_tmap_1(A_647, B_648, C_649, D_650) | ~m1_pre_topc(D_650, A_647) | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_647), u1_struct_0(B_648)))) | ~v1_funct_2(C_649, u1_struct_0(A_647), u1_struct_0(B_648)) | ~v1_funct_1(C_649) | ~l1_pre_topc(B_648) | ~v2_pre_topc(B_648) | v2_struct_0(B_648) | ~l1_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.33/1.57  tff(c_440, plain, (![D_650]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_650))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_650) | ~m1_pre_topc(D_650, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_438])).
% 3.33/1.57  tff(c_443, plain, (![D_650]: (k7_relat_1('#skF_3', u1_struct_0(D_650))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_650) | ~m1_pre_topc(D_650, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_48, c_405, c_440])).
% 3.33/1.57  tff(c_445, plain, (![D_651]: (k7_relat_1('#skF_3', u1_struct_0(D_651))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_651) | ~m1_pre_topc(D_651, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_443])).
% 3.33/1.57  tff(c_373, plain, (![C_622, A_623, B_624]: (v1_relat_1(C_622) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_623, B_624))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.57  tff(c_377, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_373])).
% 3.33/1.57  tff(c_384, plain, (![C_630, A_631, B_632]: (v4_relat_1(C_630, A_631) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.57  tff(c_388, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_384])).
% 3.33/1.57  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.57  tff(c_391, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_388, c_2])).
% 3.33/1.57  tff(c_394, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_391])).
% 3.33/1.57  tff(c_451, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_445, c_394])).
% 3.33/1.57  tff(c_460, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_451])).
% 3.33/1.57  tff(c_480, plain, (![E_659, C_658, D_662, B_661, A_660, H_663]: (r1_tmap_1(E_659, B_661, k2_tmap_1(A_660, B_661, C_658, E_659), H_663) | ~r1_tmap_1(k1_tsep_1(A_660, D_662, E_659), B_661, k2_tmap_1(A_660, B_661, C_658, k1_tsep_1(A_660, D_662, E_659)), H_663) | ~m1_subset_1(H_663, u1_struct_0(E_659)) | ~m1_subset_1(H_663, u1_struct_0(D_662)) | ~m1_subset_1(H_663, u1_struct_0(k1_tsep_1(A_660, D_662, E_659))) | ~m1_pre_topc(E_659, A_660) | v2_struct_0(E_659) | ~m1_pre_topc(D_662, A_660) | v2_struct_0(D_662) | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_660), u1_struct_0(B_661)))) | ~v1_funct_2(C_658, u1_struct_0(A_660), u1_struct_0(B_661)) | ~v1_funct_1(C_658) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | ~l1_pre_topc(A_660) | ~v2_pre_topc(A_660) | v2_struct_0(A_660))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.33/1.57  tff(c_482, plain, (![B_661, C_658, H_663]: (r1_tmap_1('#skF_5', B_661, k2_tmap_1('#skF_1', B_661, C_658, '#skF_5'), H_663) | ~r1_tmap_1('#skF_1', B_661, k2_tmap_1('#skF_1', B_661, C_658, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_663) | ~m1_subset_1(H_663, u1_struct_0('#skF_5')) | ~m1_subset_1(H_663, u1_struct_0('#skF_4')) | ~m1_subset_1(H_663, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_661)))) | ~v1_funct_2(C_658, u1_struct_0('#skF_1'), u1_struct_0(B_661)) | ~v1_funct_1(C_658) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_480])).
% 3.33/1.57  tff(c_486, plain, (![B_661, C_658, H_663]: (r1_tmap_1('#skF_5', B_661, k2_tmap_1('#skF_1', B_661, C_658, '#skF_5'), H_663) | ~r1_tmap_1('#skF_1', B_661, k2_tmap_1('#skF_1', B_661, C_658, '#skF_1'), H_663) | ~m1_subset_1(H_663, u1_struct_0('#skF_5')) | ~m1_subset_1(H_663, u1_struct_0('#skF_4')) | ~m1_subset_1(H_663, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_661)))) | ~v1_funct_2(C_658, u1_struct_0('#skF_1'), u1_struct_0(B_661)) | ~v1_funct_1(C_658) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_38, c_36, c_36, c_482])).
% 3.33/1.57  tff(c_498, plain, (![B_668, C_669, H_670]: (r1_tmap_1('#skF_5', B_668, k2_tmap_1('#skF_1', B_668, C_669, '#skF_5'), H_670) | ~r1_tmap_1('#skF_1', B_668, k2_tmap_1('#skF_1', B_668, C_669, '#skF_1'), H_670) | ~m1_subset_1(H_670, u1_struct_0('#skF_5')) | ~m1_subset_1(H_670, u1_struct_0('#skF_4')) | ~m1_subset_1(H_670, u1_struct_0('#skF_1')) | ~m1_subset_1(C_669, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_668)))) | ~v1_funct_2(C_669, u1_struct_0('#skF_1'), u1_struct_0(B_668)) | ~v1_funct_1(C_669) | ~l1_pre_topc(B_668) | ~v2_pre_topc(B_668) | v2_struct_0(B_668))), inference(negUnitSimplification, [status(thm)], [c_62, c_44, c_40, c_486])).
% 3.33/1.57  tff(c_500, plain, (![H_670]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_670) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_670) | ~m1_subset_1(H_670, u1_struct_0('#skF_5')) | ~m1_subset_1(H_670, u1_struct_0('#skF_4')) | ~m1_subset_1(H_670, u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_498])).
% 3.33/1.57  tff(c_503, plain, (![H_670]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_670) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_670) | ~m1_subset_1(H_670, u1_struct_0('#skF_5')) | ~m1_subset_1(H_670, u1_struct_0('#skF_4')) | ~m1_subset_1(H_670, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_460, c_500])).
% 3.33/1.57  tff(c_505, plain, (![H_671]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_671) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_671) | ~m1_subset_1(H_671, u1_struct_0('#skF_5')) | ~m1_subset_1(H_671, u1_struct_0('#skF_4')) | ~m1_subset_1(H_671, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_56, c_503])).
% 3.33/1.57  tff(c_372, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 3.33/1.57  tff(c_508, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_505, c_372])).
% 3.33/1.57  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_82, c_30, c_371, c_508])).
% 3.33/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.57  
% 3.33/1.57  Inference rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Ref     : 0
% 3.33/1.57  #Sup     : 81
% 3.33/1.57  #Fact    : 0
% 3.33/1.57  #Define  : 0
% 3.33/1.57  #Split   : 2
% 3.33/1.57  #Chain   : 0
% 3.33/1.57  #Close   : 0
% 3.33/1.57  
% 3.33/1.57  Ordering : KBO
% 3.33/1.57  
% 3.33/1.57  Simplification rules
% 3.33/1.57  ----------------------
% 3.33/1.57  #Subsume      : 7
% 3.33/1.57  #Demod        : 206
% 3.33/1.57  #Tautology    : 38
% 3.33/1.57  #SimpNegUnit  : 33
% 3.33/1.57  #BackRed      : 0
% 3.33/1.57  
% 3.33/1.57  #Partial instantiations: 0
% 3.33/1.57  #Strategies tried      : 1
% 3.33/1.57  
% 3.33/1.57  Timing (in seconds)
% 3.33/1.57  ----------------------
% 3.33/1.58  Preprocessing        : 0.39
% 3.33/1.58  Parsing              : 0.19
% 3.33/1.58  CNF conversion       : 0.06
% 3.33/1.58  Main loop            : 0.35
% 3.33/1.58  Inferencing          : 0.12
% 3.33/1.58  Reduction            : 0.12
% 3.33/1.58  Demodulation         : 0.09
% 3.33/1.58  BG Simplification    : 0.02
% 3.33/1.58  Subsumption          : 0.06
% 3.33/1.58  Abstraction          : 0.01
% 3.33/1.58  MUC search           : 0.00
% 3.33/1.58  Cooper               : 0.00
% 3.33/1.58  Total                : 0.80
% 3.33/1.58  Index Insertion      : 0.00
% 3.33/1.58  Index Deletion       : 0.00
% 3.33/1.58  Index Matching       : 0.00
% 3.33/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
