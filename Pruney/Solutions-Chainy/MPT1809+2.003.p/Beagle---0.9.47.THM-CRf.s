%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:04 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 580 expanded)
%              Number of leaves         :   37 ( 240 expanded)
%              Depth                    :   12
%              Number of atoms          :  511 (4849 expanded)
%              Number of equality atoms :   41 ( 655 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_203,negated_conjecture,(
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

tff(f_147,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_90,axiom,(
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

tff(f_143,axiom,(
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

tff(c_24,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_77,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_26,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_80,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_72])).

tff(c_81,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_75])).

tff(c_122,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_68])).

tff(c_121,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_73])).

tff(c_155,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_121,c_79])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_22,plain,(
    ! [A_290] :
      ( m1_pre_topc(A_290,A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_123,plain,(
    ! [A_550,B_551,C_552,D_553] :
      ( k2_partfun1(A_550,B_551,C_552,D_553) = k7_relat_1(C_552,D_553)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_550,B_551)))
      | ~ v1_funct_1(C_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_125,plain,(
    ! [D_553] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_553) = k7_relat_1('#skF_3',D_553)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_128,plain,(
    ! [D_553] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_553) = k7_relat_1('#skF_3',D_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_125])).

tff(c_216,plain,(
    ! [A_567,B_568,C_569,D_570] :
      ( k2_partfun1(u1_struct_0(A_567),u1_struct_0(B_568),C_569,u1_struct_0(D_570)) = k2_tmap_1(A_567,B_568,C_569,D_570)
      | ~ m1_pre_topc(D_570,A_567)
      | ~ m1_subset_1(C_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_567),u1_struct_0(B_568))))
      | ~ v1_funct_2(C_569,u1_struct_0(A_567),u1_struct_0(B_568))
      | ~ v1_funct_1(C_569)
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_218,plain,(
    ! [D_570] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_570)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_570)
      | ~ m1_pre_topc(D_570,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_216])).

tff(c_221,plain,(
    ! [D_570] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_570)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_570)
      | ~ m1_pre_topc(D_570,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_128,c_218])).

tff(c_223,plain,(
    ! [D_571] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_571)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_571)
      | ~ m1_pre_topc(D_571,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_221])).

tff(c_95,plain,(
    ! [C_539,A_540,B_541] :
      ( v1_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_540,B_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_95])).

tff(c_105,plain,(
    ! [C_545,A_546,B_547] :
      ( v4_relat_1(C_545,A_546)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_546,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    v4_relat_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,
    ( k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_116,plain,(
    k7_relat_1('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_113])).

tff(c_229,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_116])).

tff(c_238,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_252,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_238])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_252])).

tff(c_257,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_312,plain,(
    ! [B_595,C_598,H_597,D_599,A_594,E_596] :
      ( r1_tmap_1(k1_tsep_1(A_594,D_599,E_596),B_595,k2_tmap_1(A_594,B_595,C_598,k1_tsep_1(A_594,D_599,E_596)),H_597)
      | ~ r1_tmap_1(E_596,B_595,k2_tmap_1(A_594,B_595,C_598,E_596),H_597)
      | ~ r1_tmap_1(D_599,B_595,k2_tmap_1(A_594,B_595,C_598,D_599),H_597)
      | ~ m1_subset_1(H_597,u1_struct_0(E_596))
      | ~ m1_subset_1(H_597,u1_struct_0(D_599))
      | ~ m1_subset_1(H_597,u1_struct_0(k1_tsep_1(A_594,D_599,E_596)))
      | ~ m1_pre_topc(E_596,A_594)
      | v2_struct_0(E_596)
      | ~ m1_pre_topc(D_599,A_594)
      | v2_struct_0(D_599)
      | ~ m1_subset_1(C_598,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_594),u1_struct_0(B_595))))
      | ~ v1_funct_2(C_598,u1_struct_0(A_594),u1_struct_0(B_595))
      | ~ v1_funct_1(C_598)
      | ~ l1_pre_topc(B_595)
      | ~ v2_pre_topc(B_595)
      | v2_struct_0(B_595)
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_314,plain,(
    ! [D_599,E_596,H_597] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_599,E_596),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_599,E_596)),H_597)
      | ~ r1_tmap_1(E_596,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_596),H_597)
      | ~ r1_tmap_1(D_599,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_599),H_597)
      | ~ m1_subset_1(H_597,u1_struct_0(E_596))
      | ~ m1_subset_1(H_597,u1_struct_0(D_599))
      | ~ m1_subset_1(H_597,u1_struct_0(k1_tsep_1('#skF_1',D_599,E_596)))
      | ~ m1_pre_topc(E_596,'#skF_1')
      | v2_struct_0(E_596)
      | ~ m1_pre_topc(D_599,'#skF_1')
      | v2_struct_0(D_599)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_312])).

tff(c_317,plain,(
    ! [D_599,E_596,H_597] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_599,E_596),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_599,E_596)),H_597)
      | ~ r1_tmap_1(E_596,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_596),H_597)
      | ~ r1_tmap_1(D_599,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_599),H_597)
      | ~ m1_subset_1(H_597,u1_struct_0(E_596))
      | ~ m1_subset_1(H_597,u1_struct_0(D_599))
      | ~ m1_subset_1(H_597,u1_struct_0(k1_tsep_1('#skF_1',D_599,E_596)))
      | ~ m1_pre_topc(E_596,'#skF_1')
      | v2_struct_0(E_596)
      | ~ m1_pre_topc(D_599,'#skF_1')
      | v2_struct_0(D_599)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_314])).

tff(c_327,plain,(
    ! [D_604,E_605,H_606] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_604,E_605),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_604,E_605)),H_606)
      | ~ r1_tmap_1(E_605,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_605),H_606)
      | ~ r1_tmap_1(D_604,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_604),H_606)
      | ~ m1_subset_1(H_606,u1_struct_0(E_605))
      | ~ m1_subset_1(H_606,u1_struct_0(D_604))
      | ~ m1_subset_1(H_606,u1_struct_0(k1_tsep_1('#skF_1',D_604,E_605)))
      | ~ m1_pre_topc(E_605,'#skF_1')
      | v2_struct_0(E_605)
      | ~ m1_pre_topc(D_604,'#skF_1')
      | v2_struct_0(D_604) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_317])).

tff(c_334,plain,(
    ! [H_606] :
      ( r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_606)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_606)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_606)
      | ~ m1_subset_1(H_606,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_606,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_606,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_327])).

tff(c_347,plain,(
    ! [H_606] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_606)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_606)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_606)
      | ~ m1_subset_1(H_606,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_606,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_606,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_257,c_34,c_334])).

tff(c_352,plain,(
    ! [H_607] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_607)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_607)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_607)
      | ~ m1_subset_1(H_607,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_607,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_607,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_347])).

tff(c_358,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_121,c_352])).

tff(c_362,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80,c_28,c_122,c_358])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_362])).

tff(c_365,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_367,plain,(
    ! [A_608,B_609,C_610,D_611] :
      ( k2_partfun1(A_608,B_609,C_610,D_611) = k7_relat_1(C_610,D_611)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(k2_zfmisc_1(A_608,B_609)))
      | ~ v1_funct_1(C_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_369,plain,(
    ! [D_611] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_611) = k7_relat_1('#skF_3',D_611)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_367])).

tff(c_372,plain,(
    ! [D_611] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_611) = k7_relat_1('#skF_3',D_611) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_369])).

tff(c_460,plain,(
    ! [A_625,B_626,C_627,D_628] :
      ( k2_partfun1(u1_struct_0(A_625),u1_struct_0(B_626),C_627,u1_struct_0(D_628)) = k2_tmap_1(A_625,B_626,C_627,D_628)
      | ~ m1_pre_topc(D_628,A_625)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_625),u1_struct_0(B_626))))
      | ~ v1_funct_2(C_627,u1_struct_0(A_625),u1_struct_0(B_626))
      | ~ v1_funct_1(C_627)
      | ~ l1_pre_topc(B_626)
      | ~ v2_pre_topc(B_626)
      | v2_struct_0(B_626)
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625)
      | v2_struct_0(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_462,plain,(
    ! [D_628] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_628)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628)
      | ~ m1_pre_topc(D_628,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_460])).

tff(c_465,plain,(
    ! [D_628] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_628)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628)
      | ~ m1_pre_topc(D_628,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_372,c_462])).

tff(c_467,plain,(
    ! [D_629] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_629)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_629)
      | ~ m1_pre_topc(D_629,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_465])).

tff(c_473,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_116])).

tff(c_493,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_496,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_493])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_496])).

tff(c_501,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_536,plain,(
    ! [D_645,C_644,H_643,B_641,E_642,A_640] :
      ( r1_tmap_1(D_645,B_641,k2_tmap_1(A_640,B_641,C_644,D_645),H_643)
      | ~ r1_tmap_1(k1_tsep_1(A_640,D_645,E_642),B_641,k2_tmap_1(A_640,B_641,C_644,k1_tsep_1(A_640,D_645,E_642)),H_643)
      | ~ m1_subset_1(H_643,u1_struct_0(E_642))
      | ~ m1_subset_1(H_643,u1_struct_0(D_645))
      | ~ m1_subset_1(H_643,u1_struct_0(k1_tsep_1(A_640,D_645,E_642)))
      | ~ m1_pre_topc(E_642,A_640)
      | v2_struct_0(E_642)
      | ~ m1_pre_topc(D_645,A_640)
      | v2_struct_0(D_645)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_640),u1_struct_0(B_641))))
      | ~ v1_funct_2(C_644,u1_struct_0(A_640),u1_struct_0(B_641))
      | ~ v1_funct_1(C_644)
      | ~ l1_pre_topc(B_641)
      | ~ v2_pre_topc(B_641)
      | v2_struct_0(B_641)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_538,plain,(
    ! [B_641,C_644,H_643] :
      ( r1_tmap_1('#skF_4',B_641,k2_tmap_1('#skF_1',B_641,C_644,'#skF_4'),H_643)
      | ~ r1_tmap_1('#skF_1',B_641,k2_tmap_1('#skF_1',B_641,C_644,k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_643)
      | ~ m1_subset_1(H_643,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_643,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_641))))
      | ~ v1_funct_2(C_644,u1_struct_0('#skF_1'),u1_struct_0(B_641))
      | ~ v1_funct_1(C_644)
      | ~ l1_pre_topc(B_641)
      | ~ v2_pre_topc(B_641)
      | v2_struct_0(B_641)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_536])).

tff(c_542,plain,(
    ! [B_641,C_644,H_643] :
      ( r1_tmap_1('#skF_4',B_641,k2_tmap_1('#skF_1',B_641,C_644,'#skF_4'),H_643)
      | ~ r1_tmap_1('#skF_1',B_641,k2_tmap_1('#skF_1',B_641,C_644,'#skF_1'),H_643)
      | ~ m1_subset_1(H_643,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_643,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_643,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_641))))
      | ~ v1_funct_2(C_644,u1_struct_0('#skF_1'),u1_struct_0(B_641))
      | ~ v1_funct_1(C_644)
      | ~ l1_pre_topc(B_641)
      | ~ v2_pre_topc(B_641)
      | v2_struct_0(B_641)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_34,c_34,c_538])).

tff(c_554,plain,(
    ! [B_652,C_653,H_654] :
      ( r1_tmap_1('#skF_4',B_652,k2_tmap_1('#skF_1',B_652,C_653,'#skF_4'),H_654)
      | ~ r1_tmap_1('#skF_1',B_652,k2_tmap_1('#skF_1',B_652,C_653,'#skF_1'),H_654)
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_653,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_652))))
      | ~ v1_funct_2(C_653,u1_struct_0('#skF_1'),u1_struct_0(B_652))
      | ~ v1_funct_1(C_653)
      | ~ l1_pre_topc(B_652)
      | ~ v2_pre_topc(B_652)
      | v2_struct_0(B_652) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_542])).

tff(c_556,plain,(
    ! [H_654] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_654)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_654)
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_554])).

tff(c_558,plain,(
    ! [H_654] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_654)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_654)
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_654,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_556])).

tff(c_560,plain,(
    ! [H_655] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_655)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_655)
      | ~ m1_subset_1(H_655,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_655,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_655,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_558])).

tff(c_366,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_563,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_560,c_366])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80,c_28,c_365,c_563])).

tff(c_568,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_571,plain,(
    ! [A_656,B_657,C_658,D_659] :
      ( k2_partfun1(A_656,B_657,C_658,D_659) = k7_relat_1(C_658,D_659)
      | ~ m1_subset_1(C_658,k1_zfmisc_1(k2_zfmisc_1(A_656,B_657)))
      | ~ v1_funct_1(C_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_573,plain,(
    ! [D_659] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_659) = k7_relat_1('#skF_3',D_659)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_571])).

tff(c_576,plain,(
    ! [D_659] : k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_659) = k7_relat_1('#skF_3',D_659) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_573])).

tff(c_664,plain,(
    ! [A_673,B_674,C_675,D_676] :
      ( k2_partfun1(u1_struct_0(A_673),u1_struct_0(B_674),C_675,u1_struct_0(D_676)) = k2_tmap_1(A_673,B_674,C_675,D_676)
      | ~ m1_pre_topc(D_676,A_673)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_673),u1_struct_0(B_674))))
      | ~ v1_funct_2(C_675,u1_struct_0(A_673),u1_struct_0(B_674))
      | ~ v1_funct_1(C_675)
      | ~ l1_pre_topc(B_674)
      | ~ v2_pre_topc(B_674)
      | v2_struct_0(B_674)
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_666,plain,(
    ! [D_676] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_676)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_676)
      | ~ m1_pre_topc(D_676,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_664])).

tff(c_669,plain,(
    ! [D_676] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_676)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_676)
      | ~ m1_pre_topc(D_676,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_576,c_666])).

tff(c_671,plain,(
    ! [D_677] :
      ( k7_relat_1('#skF_3',u1_struct_0(D_677)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_677)
      | ~ m1_pre_topc(D_677,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_669])).

tff(c_677,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_116])).

tff(c_686,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_677])).

tff(c_689,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_686])).

tff(c_693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_689])).

tff(c_694,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_677])).

tff(c_696,plain,(
    ! [A_678,D_683,E_680,H_681,C_682,B_679] :
      ( r1_tmap_1(E_680,B_679,k2_tmap_1(A_678,B_679,C_682,E_680),H_681)
      | ~ r1_tmap_1(k1_tsep_1(A_678,D_683,E_680),B_679,k2_tmap_1(A_678,B_679,C_682,k1_tsep_1(A_678,D_683,E_680)),H_681)
      | ~ m1_subset_1(H_681,u1_struct_0(E_680))
      | ~ m1_subset_1(H_681,u1_struct_0(D_683))
      | ~ m1_subset_1(H_681,u1_struct_0(k1_tsep_1(A_678,D_683,E_680)))
      | ~ m1_pre_topc(E_680,A_678)
      | v2_struct_0(E_680)
      | ~ m1_pre_topc(D_683,A_678)
      | v2_struct_0(D_683)
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_678),u1_struct_0(B_679))))
      | ~ v1_funct_2(C_682,u1_struct_0(A_678),u1_struct_0(B_679))
      | ~ v1_funct_1(C_682)
      | ~ l1_pre_topc(B_679)
      | ~ v2_pre_topc(B_679)
      | v2_struct_0(B_679)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_700,plain,(
    ! [B_679,C_682,H_681] :
      ( r1_tmap_1('#skF_5',B_679,k2_tmap_1('#skF_1',B_679,C_682,'#skF_5'),H_681)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_679,k2_tmap_1('#skF_1',B_679,C_682,'#skF_1'),H_681)
      | ~ m1_subset_1(H_681,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_681,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_681,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_679))))
      | ~ v1_funct_2(C_682,u1_struct_0('#skF_1'),u1_struct_0(B_679))
      | ~ v1_funct_1(C_682)
      | ~ l1_pre_topc(B_679)
      | ~ v2_pre_topc(B_679)
      | v2_struct_0(B_679)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_696])).

tff(c_705,plain,(
    ! [B_679,C_682,H_681] :
      ( r1_tmap_1('#skF_5',B_679,k2_tmap_1('#skF_1',B_679,C_682,'#skF_5'),H_681)
      | ~ r1_tmap_1('#skF_1',B_679,k2_tmap_1('#skF_1',B_679,C_682,'#skF_1'),H_681)
      | ~ m1_subset_1(H_681,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_681,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_681,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_682,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_679))))
      | ~ v1_funct_2(C_682,u1_struct_0('#skF_1'),u1_struct_0(B_679))
      | ~ v1_funct_1(C_682)
      | ~ l1_pre_topc(B_679)
      | ~ v2_pre_topc(B_679)
      | v2_struct_0(B_679)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_36,c_34,c_34,c_700])).

tff(c_731,plain,(
    ! [B_684,C_685,H_686] :
      ( r1_tmap_1('#skF_5',B_684,k2_tmap_1('#skF_1',B_684,C_685,'#skF_5'),H_686)
      | ~ r1_tmap_1('#skF_1',B_684,k2_tmap_1('#skF_1',B_684,C_685,'#skF_1'),H_686)
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_684))))
      | ~ v1_funct_2(C_685,u1_struct_0('#skF_1'),u1_struct_0(B_684))
      | ~ v1_funct_1(C_685)
      | ~ l1_pre_topc(B_684)
      | ~ v2_pre_topc(B_684)
      | v2_struct_0(B_684) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_42,c_38,c_705])).

tff(c_733,plain,(
    ! [H_686] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_686)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_686)
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_731])).

tff(c_736,plain,(
    ! [H_686] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_686)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_686)
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_686,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_694,c_733])).

tff(c_738,plain,(
    ! [H_687] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_687)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_687)
      | ~ m1_subset_1(H_687,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_687,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_687,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_736])).

tff(c_569,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_741,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_738,c_569])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80,c_28,c_568,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:18:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.53  
% 3.32/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.53  %$ r1_tmap_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.32/1.53  
% 3.32/1.53  %Foreground sorts:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Background operators:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Foreground operators:
% 3.32/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.53  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.32/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.32/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.32/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.32/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.32/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.53  
% 3.65/1.56  tff(f_203, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 3.65/1.56  tff(f_147, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.65/1.56  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.65/1.56  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.65/1.56  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.56  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.65/1.56  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.65/1.56  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (![F]: (m1_subset_1(F, u1_struct_0(k1_tsep_1(A, D, E))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(k1_tsep_1(A, D, E), B, k2_tmap_1(A, B, C, k1_tsep_1(A, D, E)), F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 3.65/1.56  tff(c_24, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 3.65/1.56  tff(c_26, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.65/1.56  tff(c_80, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_74])).
% 3.65/1.56  tff(c_28, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_72, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_75, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_72])).
% 3.65/1.56  tff(c_81, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_75])).
% 3.65/1.56  tff(c_122, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 3.65/1.56  tff(c_68, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_76, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_68])).
% 3.65/1.56  tff(c_121, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_76])).
% 3.65/1.56  tff(c_62, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_73, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 3.65/1.56  tff(c_79, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_73])).
% 3.65/1.56  tff(c_155, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_121, c_79])).
% 3.65/1.56  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_38, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_34, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_22, plain, (![A_290]: (m1_pre_topc(A_290, A_290) | ~l1_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.65/1.56  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.65/1.56  tff(c_123, plain, (![A_550, B_551, C_552, D_553]: (k2_partfun1(A_550, B_551, C_552, D_553)=k7_relat_1(C_552, D_553) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_550, B_551))) | ~v1_funct_1(C_552))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.56  tff(c_125, plain, (![D_553]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_553)=k7_relat_1('#skF_3', D_553) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_123])).
% 3.65/1.56  tff(c_128, plain, (![D_553]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_553)=k7_relat_1('#skF_3', D_553))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_125])).
% 3.65/1.56  tff(c_216, plain, (![A_567, B_568, C_569, D_570]: (k2_partfun1(u1_struct_0(A_567), u1_struct_0(B_568), C_569, u1_struct_0(D_570))=k2_tmap_1(A_567, B_568, C_569, D_570) | ~m1_pre_topc(D_570, A_567) | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_567), u1_struct_0(B_568)))) | ~v1_funct_2(C_569, u1_struct_0(A_567), u1_struct_0(B_568)) | ~v1_funct_1(C_569) | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.65/1.56  tff(c_218, plain, (![D_570]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_570))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_570) | ~m1_pre_topc(D_570, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_216])).
% 3.65/1.56  tff(c_221, plain, (![D_570]: (k7_relat_1('#skF_3', u1_struct_0(D_570))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_570) | ~m1_pre_topc(D_570, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_128, c_218])).
% 3.65/1.56  tff(c_223, plain, (![D_571]: (k7_relat_1('#skF_3', u1_struct_0(D_571))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_571) | ~m1_pre_topc(D_571, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_221])).
% 3.65/1.56  tff(c_95, plain, (![C_539, A_540, B_541]: (v1_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_540, B_541))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.56  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_95])).
% 3.65/1.56  tff(c_105, plain, (![C_545, A_546, B_547]: (v4_relat_1(C_545, A_546) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_546, B_547))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.56  tff(c_109, plain, (v4_relat_1('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_105])).
% 3.65/1.56  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.56  tff(c_113, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_2])).
% 3.65/1.56  tff(c_116, plain, (k7_relat_1('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_113])).
% 3.65/1.56  tff(c_229, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_223, c_116])).
% 3.65/1.56  tff(c_238, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_229])).
% 3.65/1.56  tff(c_252, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_238])).
% 3.65/1.56  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_252])).
% 3.65/1.56  tff(c_257, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_229])).
% 3.65/1.56  tff(c_312, plain, (![B_595, C_598, H_597, D_599, A_594, E_596]: (r1_tmap_1(k1_tsep_1(A_594, D_599, E_596), B_595, k2_tmap_1(A_594, B_595, C_598, k1_tsep_1(A_594, D_599, E_596)), H_597) | ~r1_tmap_1(E_596, B_595, k2_tmap_1(A_594, B_595, C_598, E_596), H_597) | ~r1_tmap_1(D_599, B_595, k2_tmap_1(A_594, B_595, C_598, D_599), H_597) | ~m1_subset_1(H_597, u1_struct_0(E_596)) | ~m1_subset_1(H_597, u1_struct_0(D_599)) | ~m1_subset_1(H_597, u1_struct_0(k1_tsep_1(A_594, D_599, E_596))) | ~m1_pre_topc(E_596, A_594) | v2_struct_0(E_596) | ~m1_pre_topc(D_599, A_594) | v2_struct_0(D_599) | ~m1_subset_1(C_598, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_594), u1_struct_0(B_595)))) | ~v1_funct_2(C_598, u1_struct_0(A_594), u1_struct_0(B_595)) | ~v1_funct_1(C_598) | ~l1_pre_topc(B_595) | ~v2_pre_topc(B_595) | v2_struct_0(B_595) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.56  tff(c_314, plain, (![D_599, E_596, H_597]: (r1_tmap_1(k1_tsep_1('#skF_1', D_599, E_596), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_599, E_596)), H_597) | ~r1_tmap_1(E_596, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_596), H_597) | ~r1_tmap_1(D_599, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_599), H_597) | ~m1_subset_1(H_597, u1_struct_0(E_596)) | ~m1_subset_1(H_597, u1_struct_0(D_599)) | ~m1_subset_1(H_597, u1_struct_0(k1_tsep_1('#skF_1', D_599, E_596))) | ~m1_pre_topc(E_596, '#skF_1') | v2_struct_0(E_596) | ~m1_pre_topc(D_599, '#skF_1') | v2_struct_0(D_599) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_312])).
% 3.65/1.56  tff(c_317, plain, (![D_599, E_596, H_597]: (r1_tmap_1(k1_tsep_1('#skF_1', D_599, E_596), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_599, E_596)), H_597) | ~r1_tmap_1(E_596, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_596), H_597) | ~r1_tmap_1(D_599, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_599), H_597) | ~m1_subset_1(H_597, u1_struct_0(E_596)) | ~m1_subset_1(H_597, u1_struct_0(D_599)) | ~m1_subset_1(H_597, u1_struct_0(k1_tsep_1('#skF_1', D_599, E_596))) | ~m1_pre_topc(E_596, '#skF_1') | v2_struct_0(E_596) | ~m1_pre_topc(D_599, '#skF_1') | v2_struct_0(D_599) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_314])).
% 3.65/1.56  tff(c_327, plain, (![D_604, E_605, H_606]: (r1_tmap_1(k1_tsep_1('#skF_1', D_604, E_605), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_604, E_605)), H_606) | ~r1_tmap_1(E_605, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_605), H_606) | ~r1_tmap_1(D_604, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_604), H_606) | ~m1_subset_1(H_606, u1_struct_0(E_605)) | ~m1_subset_1(H_606, u1_struct_0(D_604)) | ~m1_subset_1(H_606, u1_struct_0(k1_tsep_1('#skF_1', D_604, E_605))) | ~m1_pre_topc(E_605, '#skF_1') | v2_struct_0(E_605) | ~m1_pre_topc(D_604, '#skF_1') | v2_struct_0(D_604))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_317])).
% 3.65/1.56  tff(c_334, plain, (![H_606]: (r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_606) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_606) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_606) | ~m1_subset_1(H_606, u1_struct_0('#skF_5')) | ~m1_subset_1(H_606, u1_struct_0('#skF_4')) | ~m1_subset_1(H_606, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_327])).
% 3.65/1.56  tff(c_347, plain, (![H_606]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_606) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_606) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_606) | ~m1_subset_1(H_606, u1_struct_0('#skF_5')) | ~m1_subset_1(H_606, u1_struct_0('#skF_4')) | ~m1_subset_1(H_606, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_257, c_34, c_334])).
% 3.65/1.56  tff(c_352, plain, (![H_607]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_607) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_607) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_607) | ~m1_subset_1(H_607, u1_struct_0('#skF_5')) | ~m1_subset_1(H_607, u1_struct_0('#skF_4')) | ~m1_subset_1(H_607, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_347])).
% 3.65/1.56  tff(c_358, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_121, c_352])).
% 3.65/1.56  tff(c_362, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_80, c_28, c_122, c_358])).
% 3.65/1.56  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_362])).
% 3.65/1.56  tff(c_365, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.65/1.56  tff(c_367, plain, (![A_608, B_609, C_610, D_611]: (k2_partfun1(A_608, B_609, C_610, D_611)=k7_relat_1(C_610, D_611) | ~m1_subset_1(C_610, k1_zfmisc_1(k2_zfmisc_1(A_608, B_609))) | ~v1_funct_1(C_610))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.56  tff(c_369, plain, (![D_611]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_611)=k7_relat_1('#skF_3', D_611) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_367])).
% 3.65/1.56  tff(c_372, plain, (![D_611]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_611)=k7_relat_1('#skF_3', D_611))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_369])).
% 3.65/1.56  tff(c_460, plain, (![A_625, B_626, C_627, D_628]: (k2_partfun1(u1_struct_0(A_625), u1_struct_0(B_626), C_627, u1_struct_0(D_628))=k2_tmap_1(A_625, B_626, C_627, D_628) | ~m1_pre_topc(D_628, A_625) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_625), u1_struct_0(B_626)))) | ~v1_funct_2(C_627, u1_struct_0(A_625), u1_struct_0(B_626)) | ~v1_funct_1(C_627) | ~l1_pre_topc(B_626) | ~v2_pre_topc(B_626) | v2_struct_0(B_626) | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625) | v2_struct_0(A_625))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.65/1.56  tff(c_462, plain, (![D_628]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_628))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628) | ~m1_pre_topc(D_628, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_460])).
% 3.65/1.56  tff(c_465, plain, (![D_628]: (k7_relat_1('#skF_3', u1_struct_0(D_628))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628) | ~m1_pre_topc(D_628, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_372, c_462])).
% 3.65/1.56  tff(c_467, plain, (![D_629]: (k7_relat_1('#skF_3', u1_struct_0(D_629))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_629) | ~m1_pre_topc(D_629, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_465])).
% 3.65/1.56  tff(c_473, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_467, c_116])).
% 3.65/1.56  tff(c_493, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_473])).
% 3.65/1.56  tff(c_496, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_493])).
% 3.65/1.56  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_496])).
% 3.65/1.56  tff(c_501, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_473])).
% 3.65/1.56  tff(c_536, plain, (![D_645, C_644, H_643, B_641, E_642, A_640]: (r1_tmap_1(D_645, B_641, k2_tmap_1(A_640, B_641, C_644, D_645), H_643) | ~r1_tmap_1(k1_tsep_1(A_640, D_645, E_642), B_641, k2_tmap_1(A_640, B_641, C_644, k1_tsep_1(A_640, D_645, E_642)), H_643) | ~m1_subset_1(H_643, u1_struct_0(E_642)) | ~m1_subset_1(H_643, u1_struct_0(D_645)) | ~m1_subset_1(H_643, u1_struct_0(k1_tsep_1(A_640, D_645, E_642))) | ~m1_pre_topc(E_642, A_640) | v2_struct_0(E_642) | ~m1_pre_topc(D_645, A_640) | v2_struct_0(D_645) | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_640), u1_struct_0(B_641)))) | ~v1_funct_2(C_644, u1_struct_0(A_640), u1_struct_0(B_641)) | ~v1_funct_1(C_644) | ~l1_pre_topc(B_641) | ~v2_pre_topc(B_641) | v2_struct_0(B_641) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.56  tff(c_538, plain, (![B_641, C_644, H_643]: (r1_tmap_1('#skF_4', B_641, k2_tmap_1('#skF_1', B_641, C_644, '#skF_4'), H_643) | ~r1_tmap_1('#skF_1', B_641, k2_tmap_1('#skF_1', B_641, C_644, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_643) | ~m1_subset_1(H_643, u1_struct_0('#skF_5')) | ~m1_subset_1(H_643, u1_struct_0('#skF_4')) | ~m1_subset_1(H_643, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_641)))) | ~v1_funct_2(C_644, u1_struct_0('#skF_1'), u1_struct_0(B_641)) | ~v1_funct_1(C_644) | ~l1_pre_topc(B_641) | ~v2_pre_topc(B_641) | v2_struct_0(B_641) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_536])).
% 3.65/1.56  tff(c_542, plain, (![B_641, C_644, H_643]: (r1_tmap_1('#skF_4', B_641, k2_tmap_1('#skF_1', B_641, C_644, '#skF_4'), H_643) | ~r1_tmap_1('#skF_1', B_641, k2_tmap_1('#skF_1', B_641, C_644, '#skF_1'), H_643) | ~m1_subset_1(H_643, u1_struct_0('#skF_5')) | ~m1_subset_1(H_643, u1_struct_0('#skF_4')) | ~m1_subset_1(H_643, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_641)))) | ~v1_funct_2(C_644, u1_struct_0('#skF_1'), u1_struct_0(B_641)) | ~v1_funct_1(C_644) | ~l1_pre_topc(B_641) | ~v2_pre_topc(B_641) | v2_struct_0(B_641) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_34, c_34, c_538])).
% 3.65/1.56  tff(c_554, plain, (![B_652, C_653, H_654]: (r1_tmap_1('#skF_4', B_652, k2_tmap_1('#skF_1', B_652, C_653, '#skF_4'), H_654) | ~r1_tmap_1('#skF_1', B_652, k2_tmap_1('#skF_1', B_652, C_653, '#skF_1'), H_654) | ~m1_subset_1(H_654, u1_struct_0('#skF_5')) | ~m1_subset_1(H_654, u1_struct_0('#skF_4')) | ~m1_subset_1(H_654, u1_struct_0('#skF_1')) | ~m1_subset_1(C_653, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_652)))) | ~v1_funct_2(C_653, u1_struct_0('#skF_1'), u1_struct_0(B_652)) | ~v1_funct_1(C_653) | ~l1_pre_topc(B_652) | ~v2_pre_topc(B_652) | v2_struct_0(B_652))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_542])).
% 3.65/1.56  tff(c_556, plain, (![H_654]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_654) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_654) | ~m1_subset_1(H_654, u1_struct_0('#skF_5')) | ~m1_subset_1(H_654, u1_struct_0('#skF_4')) | ~m1_subset_1(H_654, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_501, c_554])).
% 3.65/1.56  tff(c_558, plain, (![H_654]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_654) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_654) | ~m1_subset_1(H_654, u1_struct_0('#skF_5')) | ~m1_subset_1(H_654, u1_struct_0('#skF_4')) | ~m1_subset_1(H_654, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_556])).
% 3.65/1.56  tff(c_560, plain, (![H_655]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_655) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_655) | ~m1_subset_1(H_655, u1_struct_0('#skF_5')) | ~m1_subset_1(H_655, u1_struct_0('#skF_4')) | ~m1_subset_1(H_655, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_558])).
% 3.65/1.56  tff(c_366, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.65/1.56  tff(c_563, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_560, c_366])).
% 3.65/1.56  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_80, c_28, c_365, c_563])).
% 3.65/1.56  tff(c_568, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_76])).
% 3.65/1.56  tff(c_571, plain, (![A_656, B_657, C_658, D_659]: (k2_partfun1(A_656, B_657, C_658, D_659)=k7_relat_1(C_658, D_659) | ~m1_subset_1(C_658, k1_zfmisc_1(k2_zfmisc_1(A_656, B_657))) | ~v1_funct_1(C_658))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.56  tff(c_573, plain, (![D_659]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_659)=k7_relat_1('#skF_3', D_659) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_571])).
% 3.65/1.56  tff(c_576, plain, (![D_659]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_659)=k7_relat_1('#skF_3', D_659))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_573])).
% 3.65/1.56  tff(c_664, plain, (![A_673, B_674, C_675, D_676]: (k2_partfun1(u1_struct_0(A_673), u1_struct_0(B_674), C_675, u1_struct_0(D_676))=k2_tmap_1(A_673, B_674, C_675, D_676) | ~m1_pre_topc(D_676, A_673) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_673), u1_struct_0(B_674)))) | ~v1_funct_2(C_675, u1_struct_0(A_673), u1_struct_0(B_674)) | ~v1_funct_1(C_675) | ~l1_pre_topc(B_674) | ~v2_pre_topc(B_674) | v2_struct_0(B_674) | ~l1_pre_topc(A_673) | ~v2_pre_topc(A_673) | v2_struct_0(A_673))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.65/1.56  tff(c_666, plain, (![D_676]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_676))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_676) | ~m1_pre_topc(D_676, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_664])).
% 3.65/1.56  tff(c_669, plain, (![D_676]: (k7_relat_1('#skF_3', u1_struct_0(D_676))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_676) | ~m1_pre_topc(D_676, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_576, c_666])).
% 3.65/1.56  tff(c_671, plain, (![D_677]: (k7_relat_1('#skF_3', u1_struct_0(D_677))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_677) | ~m1_pre_topc(D_677, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_669])).
% 3.65/1.56  tff(c_677, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_671, c_116])).
% 3.65/1.56  tff(c_686, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_677])).
% 3.65/1.56  tff(c_689, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_686])).
% 3.65/1.56  tff(c_693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_689])).
% 3.65/1.56  tff(c_694, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_677])).
% 3.65/1.56  tff(c_696, plain, (![A_678, D_683, E_680, H_681, C_682, B_679]: (r1_tmap_1(E_680, B_679, k2_tmap_1(A_678, B_679, C_682, E_680), H_681) | ~r1_tmap_1(k1_tsep_1(A_678, D_683, E_680), B_679, k2_tmap_1(A_678, B_679, C_682, k1_tsep_1(A_678, D_683, E_680)), H_681) | ~m1_subset_1(H_681, u1_struct_0(E_680)) | ~m1_subset_1(H_681, u1_struct_0(D_683)) | ~m1_subset_1(H_681, u1_struct_0(k1_tsep_1(A_678, D_683, E_680))) | ~m1_pre_topc(E_680, A_678) | v2_struct_0(E_680) | ~m1_pre_topc(D_683, A_678) | v2_struct_0(D_683) | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_678), u1_struct_0(B_679)))) | ~v1_funct_2(C_682, u1_struct_0(A_678), u1_struct_0(B_679)) | ~v1_funct_1(C_682) | ~l1_pre_topc(B_679) | ~v2_pre_topc(B_679) | v2_struct_0(B_679) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.56  tff(c_700, plain, (![B_679, C_682, H_681]: (r1_tmap_1('#skF_5', B_679, k2_tmap_1('#skF_1', B_679, C_682, '#skF_5'), H_681) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_679, k2_tmap_1('#skF_1', B_679, C_682, '#skF_1'), H_681) | ~m1_subset_1(H_681, u1_struct_0('#skF_5')) | ~m1_subset_1(H_681, u1_struct_0('#skF_4')) | ~m1_subset_1(H_681, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_679)))) | ~v1_funct_2(C_682, u1_struct_0('#skF_1'), u1_struct_0(B_679)) | ~v1_funct_1(C_682) | ~l1_pre_topc(B_679) | ~v2_pre_topc(B_679) | v2_struct_0(B_679) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_696])).
% 3.65/1.56  tff(c_705, plain, (![B_679, C_682, H_681]: (r1_tmap_1('#skF_5', B_679, k2_tmap_1('#skF_1', B_679, C_682, '#skF_5'), H_681) | ~r1_tmap_1('#skF_1', B_679, k2_tmap_1('#skF_1', B_679, C_682, '#skF_1'), H_681) | ~m1_subset_1(H_681, u1_struct_0('#skF_5')) | ~m1_subset_1(H_681, u1_struct_0('#skF_4')) | ~m1_subset_1(H_681, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_682, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_679)))) | ~v1_funct_2(C_682, u1_struct_0('#skF_1'), u1_struct_0(B_679)) | ~v1_funct_1(C_682) | ~l1_pre_topc(B_679) | ~v2_pre_topc(B_679) | v2_struct_0(B_679) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_36, c_34, c_34, c_700])).
% 3.65/1.56  tff(c_731, plain, (![B_684, C_685, H_686]: (r1_tmap_1('#skF_5', B_684, k2_tmap_1('#skF_1', B_684, C_685, '#skF_5'), H_686) | ~r1_tmap_1('#skF_1', B_684, k2_tmap_1('#skF_1', B_684, C_685, '#skF_1'), H_686) | ~m1_subset_1(H_686, u1_struct_0('#skF_5')) | ~m1_subset_1(H_686, u1_struct_0('#skF_4')) | ~m1_subset_1(H_686, u1_struct_0('#skF_1')) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_684)))) | ~v1_funct_2(C_685, u1_struct_0('#skF_1'), u1_struct_0(B_684)) | ~v1_funct_1(C_685) | ~l1_pre_topc(B_684) | ~v2_pre_topc(B_684) | v2_struct_0(B_684))), inference(negUnitSimplification, [status(thm)], [c_60, c_42, c_38, c_705])).
% 3.65/1.56  tff(c_733, plain, (![H_686]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_686) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_686) | ~m1_subset_1(H_686, u1_struct_0('#skF_5')) | ~m1_subset_1(H_686, u1_struct_0('#skF_4')) | ~m1_subset_1(H_686, u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_731])).
% 3.65/1.56  tff(c_736, plain, (![H_686]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_686) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_686) | ~m1_subset_1(H_686, u1_struct_0('#skF_5')) | ~m1_subset_1(H_686, u1_struct_0('#skF_4')) | ~m1_subset_1(H_686, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_694, c_733])).
% 3.65/1.56  tff(c_738, plain, (![H_687]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_687) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_687) | ~m1_subset_1(H_687, u1_struct_0('#skF_5')) | ~m1_subset_1(H_687, u1_struct_0('#skF_4')) | ~m1_subset_1(H_687, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_54, c_736])).
% 3.65/1.56  tff(c_569, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_76])).
% 3.65/1.56  tff(c_741, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_738, c_569])).
% 3.65/1.56  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_80, c_28, c_568, c_741])).
% 3.65/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.56  
% 3.65/1.56  Inference rules
% 3.65/1.56  ----------------------
% 3.65/1.56  #Ref     : 0
% 3.65/1.56  #Sup     : 126
% 3.65/1.56  #Fact    : 0
% 3.65/1.56  #Define  : 0
% 3.65/1.56  #Split   : 5
% 3.65/1.56  #Chain   : 0
% 3.65/1.56  #Close   : 0
% 3.65/1.56  
% 3.65/1.56  Ordering : KBO
% 3.65/1.56  
% 3.65/1.56  Simplification rules
% 3.65/1.56  ----------------------
% 3.65/1.56  #Subsume      : 14
% 3.65/1.56  #Demod        : 259
% 3.65/1.56  #Tautology    : 63
% 3.65/1.56  #SimpNegUnit  : 63
% 3.65/1.56  #BackRed      : 0
% 3.65/1.56  
% 3.65/1.56  #Partial instantiations: 0
% 3.65/1.56  #Strategies tried      : 1
% 3.65/1.56  
% 3.65/1.56  Timing (in seconds)
% 3.65/1.56  ----------------------
% 3.65/1.56  Preprocessing        : 0.40
% 3.65/1.56  Parsing              : 0.19
% 3.65/1.56  CNF conversion       : 0.06
% 3.65/1.56  Main loop            : 0.38
% 3.65/1.56  Inferencing          : 0.13
% 3.65/1.56  Reduction            : 0.13
% 3.65/1.56  Demodulation         : 0.09
% 3.65/1.56  BG Simplification    : 0.02
% 3.65/1.56  Subsumption          : 0.07
% 3.65/1.56  Abstraction          : 0.02
% 3.65/1.56  MUC search           : 0.00
% 3.65/1.56  Cooper               : 0.00
% 3.65/1.57  Total                : 0.83
% 3.65/1.57  Index Insertion      : 0.00
% 3.65/1.57  Index Deletion       : 0.00
% 3.65/1.57  Index Matching       : 0.00
% 3.65/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
