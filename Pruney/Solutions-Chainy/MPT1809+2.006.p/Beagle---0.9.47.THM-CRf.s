%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:05 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 696 expanded)
%              Number of leaves         :   31 ( 288 expanded)
%              Depth                    :   17
%              Number of atoms          :  673 (6748 expanded)
%              Number of equality atoms :   61 ( 883 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ! [H] :
                                  ( m1_subset_1(H,u1_struct_0(k1_tsep_1(A,C,D)))
                                 => ( ( H = F
                                      & H = G )
                                   => ( r1_tmap_1(k1_tsep_1(A,C,D),B,E,H)
                                    <=> ( r1_tmap_1(C,B,k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),F)
                                        & r1_tmap_1(D,B,k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),G) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).

tff(c_14,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_16,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_20,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_67,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_71,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_65])).

tff(c_86,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_58,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_85,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_52,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_63,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_69,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_63])).

tff(c_88,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_69])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_12,plain,(
    ! [A_302] :
      ( m1_pre_topc(A_302,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_105,plain,(
    ! [C_559,D_558,A_560,B_556,E_557] :
      ( k3_tmap_1(A_560,B_556,C_559,D_558,E_557) = k2_partfun1(u1_struct_0(C_559),u1_struct_0(B_556),E_557,u1_struct_0(D_558))
      | ~ m1_pre_topc(D_558,C_559)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_559),u1_struct_0(B_556))))
      | ~ v1_funct_2(E_557,u1_struct_0(C_559),u1_struct_0(B_556))
      | ~ v1_funct_1(E_557)
      | ~ m1_pre_topc(D_558,A_560)
      | ~ m1_pre_topc(C_559,A_560)
      | ~ l1_pre_topc(B_556)
      | ~ v2_pre_topc(B_556)
      | v2_struct_0(B_556)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_107,plain,(
    ! [A_560,D_558] :
      ( k3_tmap_1(A_560,'#skF_2','#skF_1',D_558,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_558))
      | ~ m1_pre_topc(D_558,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_558,A_560)
      | ~ m1_pre_topc('#skF_1',A_560)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_110,plain,(
    ! [A_560,D_558] :
      ( k3_tmap_1(A_560,'#skF_2','#skF_1',D_558,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_558))
      | ~ m1_pre_topc(D_558,'#skF_1')
      | ~ m1_pre_topc(D_558,A_560)
      | ~ m1_pre_topc('#skF_1',A_560)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_107])).

tff(c_112,plain,(
    ! [A_561,D_562] :
      ( k3_tmap_1(A_561,'#skF_2','#skF_1',D_562,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_562))
      | ~ m1_pre_topc(D_562,'#skF_1')
      | ~ m1_pre_topc(D_562,A_561)
      | ~ m1_pre_topc('#skF_1',A_561)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_110])).

tff(c_116,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_122,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_116])).

tff(c_123,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_122])).

tff(c_128,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_136,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_89,plain,(
    ! [A_551,B_552,C_553,D_554] :
      ( k2_partfun1(u1_struct_0(A_551),u1_struct_0(B_552),C_553,u1_struct_0(D_554)) = k2_tmap_1(A_551,B_552,C_553,D_554)
      | ~ m1_pre_topc(D_554,A_551)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_551),u1_struct_0(B_552))))
      | ~ v1_funct_2(C_553,u1_struct_0(A_551),u1_struct_0(B_552))
      | ~ v1_funct_1(C_553)
      | ~ l1_pre_topc(B_552)
      | ~ v2_pre_topc(B_552)
      | v2_struct_0(B_552)
      | ~ l1_pre_topc(A_551)
      | ~ v2_pre_topc(A_551)
      | v2_struct_0(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91,plain,(
    ! [D_554] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_554)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_554)
      | ~ m1_pre_topc(D_554,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_94,plain,(
    ! [D_554] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_554)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_554)
      | ~ m1_pre_topc(D_554,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_38,c_36,c_91])).

tff(c_95,plain,(
    ! [D_554] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_554)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_554)
      | ~ m1_pre_topc(D_554,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_94])).

tff(c_147,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_95])).

tff(c_154,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_147])).

tff(c_26,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_137,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_118,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_126,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_26,c_118])).

tff(c_127,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_126])).

tff(c_206,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_127])).

tff(c_210,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_95])).

tff(c_217,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_210])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_24,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_353,plain,(
    ! [A_577,H_580,D_579,E_582,B_581,C_578] :
      ( r1_tmap_1(k1_tsep_1(A_577,C_578,D_579),B_581,E_582,H_580)
      | ~ r1_tmap_1(D_579,B_581,k3_tmap_1(A_577,B_581,k1_tsep_1(A_577,C_578,D_579),D_579,E_582),H_580)
      | ~ r1_tmap_1(C_578,B_581,k3_tmap_1(A_577,B_581,k1_tsep_1(A_577,C_578,D_579),C_578,E_582),H_580)
      | ~ m1_subset_1(H_580,u1_struct_0(k1_tsep_1(A_577,C_578,D_579)))
      | ~ m1_subset_1(H_580,u1_struct_0(D_579))
      | ~ m1_subset_1(H_580,u1_struct_0(C_578))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_577,C_578,D_579)),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0(k1_tsep_1(A_577,C_578,D_579)),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | ~ m1_pre_topc(D_579,A_577)
      | v2_struct_0(D_579)
      | ~ m1_pre_topc(C_578,A_577)
      | v2_struct_0(C_578)
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_355,plain,(
    ! [B_581,E_582,H_580] :
      ( r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_581,E_582,H_580)
      | ~ r1_tmap_1('#skF_5',B_581,k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_5',E_582),H_580)
      | ~ r1_tmap_1('#skF_4',B_581,k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_582),H_580)
      | ~ m1_subset_1(H_580,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_580,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_580,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_353])).

tff(c_357,plain,(
    ! [B_581,E_582,H_580] :
      ( r1_tmap_1('#skF_1',B_581,E_582,H_580)
      | ~ r1_tmap_1('#skF_5',B_581,k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_5',E_582),H_580)
      | ~ r1_tmap_1('#skF_4',B_581,k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582),H_580)
      | ~ m1_subset_1(H_580,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_580,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_580,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0('#skF_1'),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_26,c_24,c_24,c_24,c_24,c_24,c_355])).

tff(c_375,plain,(
    ! [B_591,E_592,H_593] :
      ( r1_tmap_1('#skF_1',B_591,E_592,H_593)
      | ~ r1_tmap_1('#skF_5',B_591,k3_tmap_1('#skF_1',B_591,'#skF_1','#skF_5',E_592),H_593)
      | ~ r1_tmap_1('#skF_4',B_591,k3_tmap_1('#skF_1',B_591,'#skF_1','#skF_4',E_592),H_593)
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_592,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_591))))
      | ~ v1_funct_2(E_592,u1_struct_0('#skF_1'),u1_struct_0(B_591))
      | ~ v1_funct_1(E_592)
      | ~ l1_pre_topc(B_591)
      | ~ v2_pre_topc(B_591)
      | v2_struct_0(B_591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_32,c_28,c_357])).

tff(c_377,plain,(
    ! [H_593] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_593)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_593)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),H_593)
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_375])).

tff(c_379,plain,(
    ! [H_593] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_593)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_593)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_593)
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_593,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_154,c_377])).

tff(c_381,plain,(
    ! [H_594] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_594)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_594)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_594)
      | ~ m1_subset_1(H_594,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_594,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_594,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_379])).

tff(c_387,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_85,c_381])).

tff(c_391,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18,c_67,c_86,c_387])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_391])).

tff(c_394,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_414,plain,(
    ! [E_601,B_600,C_603,A_604,D_602] :
      ( k3_tmap_1(A_604,B_600,C_603,D_602,E_601) = k2_partfun1(u1_struct_0(C_603),u1_struct_0(B_600),E_601,u1_struct_0(D_602))
      | ~ m1_pre_topc(D_602,C_603)
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_603),u1_struct_0(B_600))))
      | ~ v1_funct_2(E_601,u1_struct_0(C_603),u1_struct_0(B_600))
      | ~ v1_funct_1(E_601)
      | ~ m1_pre_topc(D_602,A_604)
      | ~ m1_pre_topc(C_603,A_604)
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_416,plain,(
    ! [A_604,D_602] :
      ( k3_tmap_1(A_604,'#skF_2','#skF_1',D_602,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_602))
      | ~ m1_pre_topc(D_602,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_602,A_604)
      | ~ m1_pre_topc('#skF_1',A_604)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(resolution,[status(thm)],[c_34,c_414])).

tff(c_419,plain,(
    ! [A_604,D_602] :
      ( k3_tmap_1(A_604,'#skF_2','#skF_1',D_602,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_602))
      | ~ m1_pre_topc(D_602,'#skF_1')
      | ~ m1_pre_topc(D_602,A_604)
      | ~ m1_pre_topc('#skF_1',A_604)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_416])).

tff(c_421,plain,(
    ! [A_605,D_606] :
      ( k3_tmap_1(A_605,'#skF_2','#skF_1',D_606,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_606))
      | ~ m1_pre_topc(D_606,'#skF_1')
      | ~ m1_pre_topc(D_606,A_605)
      | ~ m1_pre_topc('#skF_1',A_605)
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_419])).

tff(c_425,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_421])).

tff(c_431,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_425])).

tff(c_432,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_431])).

tff(c_437,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_440,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_437])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_440])).

tff(c_445,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_398,plain,(
    ! [A_595,B_596,C_597,D_598] :
      ( k2_partfun1(u1_struct_0(A_595),u1_struct_0(B_596),C_597,u1_struct_0(D_598)) = k2_tmap_1(A_595,B_596,C_597,D_598)
      | ~ m1_pre_topc(D_598,A_595)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_595),u1_struct_0(B_596))))
      | ~ v1_funct_2(C_597,u1_struct_0(A_595),u1_struct_0(B_596))
      | ~ v1_funct_1(C_597)
      | ~ l1_pre_topc(B_596)
      | ~ v2_pre_topc(B_596)
      | v2_struct_0(B_596)
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595)
      | v2_struct_0(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_400,plain,(
    ! [D_598] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_598)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_598)
      | ~ m1_pre_topc(D_598,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_398])).

tff(c_403,plain,(
    ! [D_598] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_598)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_598)
      | ~ m1_pre_topc(D_598,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_38,c_36,c_400])).

tff(c_404,plain,(
    ! [D_598] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_598)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_598)
      | ~ m1_pre_topc(D_598,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_403])).

tff(c_456,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_404])).

tff(c_463,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_456])).

tff(c_569,plain,(
    ! [B_617,C_614,E_618,D_615,H_616,A_613] :
      ( r1_tmap_1(C_614,B_617,k3_tmap_1(A_613,B_617,k1_tsep_1(A_613,C_614,D_615),C_614,E_618),H_616)
      | ~ r1_tmap_1(k1_tsep_1(A_613,C_614,D_615),B_617,E_618,H_616)
      | ~ m1_subset_1(H_616,u1_struct_0(k1_tsep_1(A_613,C_614,D_615)))
      | ~ m1_subset_1(H_616,u1_struct_0(D_615))
      | ~ m1_subset_1(H_616,u1_struct_0(C_614))
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_613,C_614,D_615)),u1_struct_0(B_617))))
      | ~ v1_funct_2(E_618,u1_struct_0(k1_tsep_1(A_613,C_614,D_615)),u1_struct_0(B_617))
      | ~ v1_funct_1(E_618)
      | ~ m1_pre_topc(D_615,A_613)
      | v2_struct_0(D_615)
      | ~ m1_pre_topc(C_614,A_613)
      | v2_struct_0(C_614)
      | ~ l1_pre_topc(B_617)
      | ~ v2_pre_topc(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_571,plain,(
    ! [B_617,E_618,H_616] :
      ( r1_tmap_1('#skF_4',B_617,k3_tmap_1('#skF_1',B_617,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_618),H_616)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_617,E_618,H_616)
      | ~ m1_subset_1(H_616,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_617))))
      | ~ v1_funct_2(E_618,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_617))
      | ~ v1_funct_1(E_618)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_617)
      | ~ v2_pre_topc(B_617)
      | v2_struct_0(B_617)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_569])).

tff(c_573,plain,(
    ! [B_617,E_618,H_616] :
      ( r1_tmap_1('#skF_4',B_617,k3_tmap_1('#skF_1',B_617,'#skF_1','#skF_4',E_618),H_616)
      | ~ r1_tmap_1('#skF_1',B_617,E_618,H_616)
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_616,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_618,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_617))))
      | ~ v1_funct_2(E_618,u1_struct_0('#skF_1'),u1_struct_0(B_617))
      | ~ v1_funct_1(E_618)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_617)
      | ~ v2_pre_topc(B_617)
      | v2_struct_0(B_617)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_26,c_24,c_24,c_24,c_24,c_571])).

tff(c_676,plain,(
    ! [B_631,E_632,H_633] :
      ( r1_tmap_1('#skF_4',B_631,k3_tmap_1('#skF_1',B_631,'#skF_1','#skF_4',E_632),H_633)
      | ~ r1_tmap_1('#skF_1',B_631,E_632,H_633)
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_632,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_631))))
      | ~ v1_funct_2(E_632,u1_struct_0('#skF_1'),u1_struct_0(B_631))
      | ~ v1_funct_1(E_632)
      | ~ l1_pre_topc(B_631)
      | ~ v2_pre_topc(B_631)
      | v2_struct_0(B_631) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_32,c_28,c_573])).

tff(c_678,plain,(
    ! [H_633] :
      ( r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),H_633)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_633)
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_676])).

tff(c_681,plain,(
    ! [H_633] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_633)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_633)
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_633,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_463,c_678])).

tff(c_683,plain,(
    ! [H_634] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_634)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_634)
      | ~ m1_subset_1(H_634,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_634,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_634,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_681])).

tff(c_395,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_686,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_683,c_395])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18,c_67,c_394,c_686])).

tff(c_691,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_703,plain,(
    ! [B_639,D_641,E_640,C_642,A_643] :
      ( k3_tmap_1(A_643,B_639,C_642,D_641,E_640) = k2_partfun1(u1_struct_0(C_642),u1_struct_0(B_639),E_640,u1_struct_0(D_641))
      | ~ m1_pre_topc(D_641,C_642)
      | ~ m1_subset_1(E_640,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_642),u1_struct_0(B_639))))
      | ~ v1_funct_2(E_640,u1_struct_0(C_642),u1_struct_0(B_639))
      | ~ v1_funct_1(E_640)
      | ~ m1_pre_topc(D_641,A_643)
      | ~ m1_pre_topc(C_642,A_643)
      | ~ l1_pre_topc(B_639)
      | ~ v2_pre_topc(B_639)
      | v2_struct_0(B_639)
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_705,plain,(
    ! [A_643,D_641] :
      ( k3_tmap_1(A_643,'#skF_2','#skF_1',D_641,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_641))
      | ~ m1_pre_topc(D_641,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_641,A_643)
      | ~ m1_pre_topc('#skF_1',A_643)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(resolution,[status(thm)],[c_34,c_703])).

tff(c_708,plain,(
    ! [A_643,D_641] :
      ( k3_tmap_1(A_643,'#skF_2','#skF_1',D_641,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_641))
      | ~ m1_pre_topc(D_641,'#skF_1')
      | ~ m1_pre_topc(D_641,A_643)
      | ~ m1_pre_topc('#skF_1',A_643)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_705])).

tff(c_719,plain,(
    ! [A_645,D_646] :
      ( k3_tmap_1(A_645,'#skF_2','#skF_1',D_646,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_646))
      | ~ m1_pre_topc(D_646,'#skF_1')
      | ~ m1_pre_topc(D_646,A_645)
      | ~ m1_pre_topc('#skF_1',A_645)
      | ~ l1_pre_topc(A_645)
      | ~ v2_pre_topc(A_645)
      | v2_struct_0(A_645) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_708])).

tff(c_723,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_719])).

tff(c_729,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_723])).

tff(c_730,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_729])).

tff(c_735,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_739,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_735])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_739])).

tff(c_745,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_725,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_719])).

tff(c_733,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_26,c_725])).

tff(c_734,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_733])).

tff(c_814,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_734])).

tff(c_696,plain,(
    ! [A_635,B_636,C_637,D_638] :
      ( k2_partfun1(u1_struct_0(A_635),u1_struct_0(B_636),C_637,u1_struct_0(D_638)) = k2_tmap_1(A_635,B_636,C_637,D_638)
      | ~ m1_pre_topc(D_638,A_635)
      | ~ m1_subset_1(C_637,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_635),u1_struct_0(B_636))))
      | ~ v1_funct_2(C_637,u1_struct_0(A_635),u1_struct_0(B_636))
      | ~ v1_funct_1(C_637)
      | ~ l1_pre_topc(B_636)
      | ~ v2_pre_topc(B_636)
      | v2_struct_0(B_636)
      | ~ l1_pre_topc(A_635)
      | ~ v2_pre_topc(A_635)
      | v2_struct_0(A_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_698,plain,(
    ! [D_638] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_638)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_638)
      | ~ m1_pre_topc(D_638,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_696])).

tff(c_701,plain,(
    ! [D_638] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_638)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_638)
      | ~ m1_pre_topc(D_638,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_38,c_36,c_698])).

tff(c_702,plain,(
    ! [D_638] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_638)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_638)
      | ~ m1_pre_topc(D_638,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_701])).

tff(c_818,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_702])).

tff(c_825,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_818])).

tff(c_868,plain,(
    ! [D_655,A_653,C_654,H_656,E_658,B_657] :
      ( r1_tmap_1(D_655,B_657,k3_tmap_1(A_653,B_657,k1_tsep_1(A_653,C_654,D_655),D_655,E_658),H_656)
      | ~ r1_tmap_1(k1_tsep_1(A_653,C_654,D_655),B_657,E_658,H_656)
      | ~ m1_subset_1(H_656,u1_struct_0(k1_tsep_1(A_653,C_654,D_655)))
      | ~ m1_subset_1(H_656,u1_struct_0(D_655))
      | ~ m1_subset_1(H_656,u1_struct_0(C_654))
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_653,C_654,D_655)),u1_struct_0(B_657))))
      | ~ v1_funct_2(E_658,u1_struct_0(k1_tsep_1(A_653,C_654,D_655)),u1_struct_0(B_657))
      | ~ v1_funct_1(E_658)
      | ~ m1_pre_topc(D_655,A_653)
      | v2_struct_0(D_655)
      | ~ m1_pre_topc(C_654,A_653)
      | v2_struct_0(C_654)
      | ~ l1_pre_topc(B_657)
      | ~ v2_pre_topc(B_657)
      | v2_struct_0(B_657)
      | ~ l1_pre_topc(A_653)
      | ~ v2_pre_topc(A_653)
      | v2_struct_0(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_870,plain,(
    ! [B_657,E_658,H_656] :
      ( r1_tmap_1('#skF_5',B_657,k3_tmap_1('#skF_1',B_657,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_658),H_656)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_657,E_658,H_656)
      | ~ m1_subset_1(H_656,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_656,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_656,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_657))))
      | ~ v1_funct_2(E_658,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_657))
      | ~ v1_funct_1(E_658)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_657)
      | ~ v2_pre_topc(B_657)
      | v2_struct_0(B_657)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_868])).

tff(c_872,plain,(
    ! [B_657,E_658,H_656] :
      ( r1_tmap_1('#skF_5',B_657,k3_tmap_1('#skF_1',B_657,'#skF_1','#skF_5',E_658),H_656)
      | ~ r1_tmap_1('#skF_1',B_657,E_658,H_656)
      | ~ m1_subset_1(H_656,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_656,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_656,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_657))))
      | ~ v1_funct_2(E_658,u1_struct_0('#skF_1'),u1_struct_0(B_657))
      | ~ v1_funct_1(E_658)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_657)
      | ~ v2_pre_topc(B_657)
      | v2_struct_0(B_657)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_30,c_26,c_24,c_24,c_24,c_24,c_870])).

tff(c_975,plain,(
    ! [B_671,E_672,H_673] :
      ( r1_tmap_1('#skF_5',B_671,k3_tmap_1('#skF_1',B_671,'#skF_1','#skF_5',E_672),H_673)
      | ~ r1_tmap_1('#skF_1',B_671,E_672,H_673)
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_671))))
      | ~ v1_funct_2(E_672,u1_struct_0('#skF_1'),u1_struct_0(B_671))
      | ~ v1_funct_1(E_672)
      | ~ l1_pre_topc(B_671)
      | ~ v2_pre_topc(B_671)
      | v2_struct_0(B_671) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_32,c_28,c_872])).

tff(c_977,plain,(
    ! [H_673] :
      ( r1_tmap_1('#skF_5','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),H_673)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_673)
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_975])).

tff(c_980,plain,(
    ! [H_673] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_673)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_673)
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_673,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_825,c_977])).

tff(c_982,plain,(
    ! [H_674] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_674)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_674)
      | ~ m1_subset_1(H_674,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_674,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_674,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_980])).

tff(c_692,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_985,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_982,c_692])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18,c_67,c_691,c_985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.61  
% 3.60/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.61  %$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.89/1.61  
% 3.89/1.61  %Foreground sorts:
% 3.89/1.61  
% 3.89/1.61  
% 3.89/1.61  %Background operators:
% 3.89/1.61  
% 3.89/1.61  
% 3.89/1.61  %Foreground operators:
% 3.89/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.89/1.61  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.89/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.89/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.89/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.89/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.89/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.89/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.89/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.89/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.89/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.89/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.89/1.61  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.89/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.89/1.61  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.89/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.89/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.61  
% 3.89/1.63  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_tmap_1)).
% 3.89/1.63  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.89/1.63  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.89/1.63  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.89/1.63  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(k1_tsep_1(A, C, D))) => (((H = F) & (H = G)) => (r1_tmap_1(k1_tsep_1(A, C, D), B, E, H) <=> (r1_tmap_1(C, B, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), F) & r1_tmap_1(D, B, k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), G)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_tmap_1)).
% 3.89/1.63  tff(c_14, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_16, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_20, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 3.89/1.63  tff(c_70, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_64])).
% 3.89/1.63  tff(c_18, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_22, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_67, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 3.89/1.63  tff(c_62, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_65, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 3.89/1.63  tff(c_71, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_65])).
% 3.89/1.63  tff(c_86, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_71])).
% 3.89/1.63  tff(c_58, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_66, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 3.89/1.63  tff(c_85, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 3.89/1.63  tff(c_52, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_63, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 3.89/1.63  tff(c_69, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_63])).
% 3.89/1.63  tff(c_88, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_69])).
% 3.89/1.63  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_36, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.63  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_12, plain, (![A_302]: (m1_pre_topc(A_302, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.89/1.64  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_105, plain, (![C_559, D_558, A_560, B_556, E_557]: (k3_tmap_1(A_560, B_556, C_559, D_558, E_557)=k2_partfun1(u1_struct_0(C_559), u1_struct_0(B_556), E_557, u1_struct_0(D_558)) | ~m1_pre_topc(D_558, C_559) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_559), u1_struct_0(B_556)))) | ~v1_funct_2(E_557, u1_struct_0(C_559), u1_struct_0(B_556)) | ~v1_funct_1(E_557) | ~m1_pre_topc(D_558, A_560) | ~m1_pre_topc(C_559, A_560) | ~l1_pre_topc(B_556) | ~v2_pre_topc(B_556) | v2_struct_0(B_556) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.89/1.64  tff(c_107, plain, (![A_560, D_558]: (k3_tmap_1(A_560, '#skF_2', '#skF_1', D_558, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_558)) | ~m1_pre_topc(D_558, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_558, A_560) | ~m1_pre_topc('#skF_1', A_560) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(resolution, [status(thm)], [c_34, c_105])).
% 3.89/1.64  tff(c_110, plain, (![A_560, D_558]: (k3_tmap_1(A_560, '#skF_2', '#skF_1', D_558, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_558)) | ~m1_pre_topc(D_558, '#skF_1') | ~m1_pre_topc(D_558, A_560) | ~m1_pre_topc('#skF_1', A_560) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_107])).
% 3.89/1.64  tff(c_112, plain, (![A_561, D_562]: (k3_tmap_1(A_561, '#skF_2', '#skF_1', D_562, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_562)) | ~m1_pre_topc(D_562, '#skF_1') | ~m1_pre_topc(D_562, A_561) | ~m1_pre_topc('#skF_1', A_561) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(negUnitSimplification, [status(thm)], [c_44, c_110])).
% 3.89/1.64  tff(c_116, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_112])).
% 3.89/1.64  tff(c_122, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_116])).
% 3.89/1.64  tff(c_123, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_122])).
% 3.89/1.64  tff(c_128, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_123])).
% 3.89/1.64  tff(c_131, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_128])).
% 3.89/1.64  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_131])).
% 3.89/1.64  tff(c_136, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_123])).
% 3.89/1.64  tff(c_89, plain, (![A_551, B_552, C_553, D_554]: (k2_partfun1(u1_struct_0(A_551), u1_struct_0(B_552), C_553, u1_struct_0(D_554))=k2_tmap_1(A_551, B_552, C_553, D_554) | ~m1_pre_topc(D_554, A_551) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_551), u1_struct_0(B_552)))) | ~v1_funct_2(C_553, u1_struct_0(A_551), u1_struct_0(B_552)) | ~v1_funct_1(C_553) | ~l1_pre_topc(B_552) | ~v2_pre_topc(B_552) | v2_struct_0(B_552) | ~l1_pre_topc(A_551) | ~v2_pre_topc(A_551) | v2_struct_0(A_551))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.89/1.64  tff(c_91, plain, (![D_554]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_554))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_554) | ~m1_pre_topc(D_554, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_89])).
% 3.89/1.64  tff(c_94, plain, (![D_554]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_554))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_554) | ~m1_pre_topc(D_554, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_38, c_36, c_91])).
% 3.89/1.64  tff(c_95, plain, (![D_554]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_554))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_554) | ~m1_pre_topc(D_554, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_94])).
% 3.89/1.64  tff(c_147, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_95])).
% 3.89/1.64  tff(c_154, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_147])).
% 3.89/1.64  tff(c_26, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_137, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_123])).
% 3.89/1.64  tff(c_118, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_112])).
% 3.89/1.64  tff(c_126, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_26, c_118])).
% 3.89/1.64  tff(c_127, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_126])).
% 3.89/1.64  tff(c_206, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_127])).
% 3.89/1.64  tff(c_210, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_206, c_95])).
% 3.89/1.64  tff(c_217, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_210])).
% 3.89/1.64  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_28, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_24, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.89/1.64  tff(c_353, plain, (![A_577, H_580, D_579, E_582, B_581, C_578]: (r1_tmap_1(k1_tsep_1(A_577, C_578, D_579), B_581, E_582, H_580) | ~r1_tmap_1(D_579, B_581, k3_tmap_1(A_577, B_581, k1_tsep_1(A_577, C_578, D_579), D_579, E_582), H_580) | ~r1_tmap_1(C_578, B_581, k3_tmap_1(A_577, B_581, k1_tsep_1(A_577, C_578, D_579), C_578, E_582), H_580) | ~m1_subset_1(H_580, u1_struct_0(k1_tsep_1(A_577, C_578, D_579))) | ~m1_subset_1(H_580, u1_struct_0(D_579)) | ~m1_subset_1(H_580, u1_struct_0(C_578)) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_577, C_578, D_579)), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0(k1_tsep_1(A_577, C_578, D_579)), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | ~m1_pre_topc(D_579, A_577) | v2_struct_0(D_579) | ~m1_pre_topc(C_578, A_577) | v2_struct_0(C_578) | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.89/1.64  tff(c_355, plain, (![B_581, E_582, H_580]: (r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_581, E_582, H_580) | ~r1_tmap_1('#skF_5', B_581, k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_5', E_582), H_580) | ~r1_tmap_1('#skF_4', B_581, k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_582), H_580) | ~m1_subset_1(H_580, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_580, u1_struct_0('#skF_5')) | ~m1_subset_1(H_580, u1_struct_0('#skF_4')) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_353])).
% 3.89/1.64  tff(c_357, plain, (![B_581, E_582, H_580]: (r1_tmap_1('#skF_1', B_581, E_582, H_580) | ~r1_tmap_1('#skF_5', B_581, k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_5', E_582), H_580) | ~r1_tmap_1('#skF_4', B_581, k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582), H_580) | ~m1_subset_1(H_580, u1_struct_0('#skF_1')) | ~m1_subset_1(H_580, u1_struct_0('#skF_5')) | ~m1_subset_1(H_580, u1_struct_0('#skF_4')) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0('#skF_1'), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_26, c_24, c_24, c_24, c_24, c_24, c_355])).
% 3.89/1.64  tff(c_375, plain, (![B_591, E_592, H_593]: (r1_tmap_1('#skF_1', B_591, E_592, H_593) | ~r1_tmap_1('#skF_5', B_591, k3_tmap_1('#skF_1', B_591, '#skF_1', '#skF_5', E_592), H_593) | ~r1_tmap_1('#skF_4', B_591, k3_tmap_1('#skF_1', B_591, '#skF_1', '#skF_4', E_592), H_593) | ~m1_subset_1(H_593, u1_struct_0('#skF_1')) | ~m1_subset_1(H_593, u1_struct_0('#skF_5')) | ~m1_subset_1(H_593, u1_struct_0('#skF_4')) | ~m1_subset_1(E_592, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_591)))) | ~v1_funct_2(E_592, u1_struct_0('#skF_1'), u1_struct_0(B_591)) | ~v1_funct_1(E_592) | ~l1_pre_topc(B_591) | ~v2_pre_topc(B_591) | v2_struct_0(B_591))), inference(negUnitSimplification, [status(thm)], [c_50, c_32, c_28, c_357])).
% 3.89/1.64  tff(c_377, plain, (![H_593]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_593) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_593) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), H_593) | ~m1_subset_1(H_593, u1_struct_0('#skF_1')) | ~m1_subset_1(H_593, u1_struct_0('#skF_5')) | ~m1_subset_1(H_593, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_217, c_375])).
% 3.89/1.64  tff(c_379, plain, (![H_593]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_593) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_593) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_593) | ~m1_subset_1(H_593, u1_struct_0('#skF_1')) | ~m1_subset_1(H_593, u1_struct_0('#skF_5')) | ~m1_subset_1(H_593, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_154, c_377])).
% 3.89/1.64  tff(c_381, plain, (![H_594]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_594) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_594) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_594) | ~m1_subset_1(H_594, u1_struct_0('#skF_1')) | ~m1_subset_1(H_594, u1_struct_0('#skF_5')) | ~m1_subset_1(H_594, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_379])).
% 3.89/1.64  tff(c_387, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_85, c_381])).
% 3.89/1.64  tff(c_391, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18, c_67, c_86, c_387])).
% 3.89/1.64  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_391])).
% 3.89/1.64  tff(c_394, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_71])).
% 3.89/1.64  tff(c_414, plain, (![E_601, B_600, C_603, A_604, D_602]: (k3_tmap_1(A_604, B_600, C_603, D_602, E_601)=k2_partfun1(u1_struct_0(C_603), u1_struct_0(B_600), E_601, u1_struct_0(D_602)) | ~m1_pre_topc(D_602, C_603) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_603), u1_struct_0(B_600)))) | ~v1_funct_2(E_601, u1_struct_0(C_603), u1_struct_0(B_600)) | ~v1_funct_1(E_601) | ~m1_pre_topc(D_602, A_604) | ~m1_pre_topc(C_603, A_604) | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.89/1.64  tff(c_416, plain, (![A_604, D_602]: (k3_tmap_1(A_604, '#skF_2', '#skF_1', D_602, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_602)) | ~m1_pre_topc(D_602, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_602, A_604) | ~m1_pre_topc('#skF_1', A_604) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(resolution, [status(thm)], [c_34, c_414])).
% 3.89/1.64  tff(c_419, plain, (![A_604, D_602]: (k3_tmap_1(A_604, '#skF_2', '#skF_1', D_602, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_602)) | ~m1_pre_topc(D_602, '#skF_1') | ~m1_pre_topc(D_602, A_604) | ~m1_pre_topc('#skF_1', A_604) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_416])).
% 3.89/1.64  tff(c_421, plain, (![A_605, D_606]: (k3_tmap_1(A_605, '#skF_2', '#skF_1', D_606, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_606)) | ~m1_pre_topc(D_606, '#skF_1') | ~m1_pre_topc(D_606, A_605) | ~m1_pre_topc('#skF_1', A_605) | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(negUnitSimplification, [status(thm)], [c_44, c_419])).
% 3.89/1.64  tff(c_425, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_421])).
% 3.89/1.64  tff(c_431, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_425])).
% 3.89/1.64  tff(c_432, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_431])).
% 3.89/1.64  tff(c_437, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_432])).
% 3.89/1.64  tff(c_440, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_437])).
% 3.89/1.64  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_440])).
% 3.89/1.64  tff(c_445, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_432])).
% 3.89/1.64  tff(c_398, plain, (![A_595, B_596, C_597, D_598]: (k2_partfun1(u1_struct_0(A_595), u1_struct_0(B_596), C_597, u1_struct_0(D_598))=k2_tmap_1(A_595, B_596, C_597, D_598) | ~m1_pre_topc(D_598, A_595) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_595), u1_struct_0(B_596)))) | ~v1_funct_2(C_597, u1_struct_0(A_595), u1_struct_0(B_596)) | ~v1_funct_1(C_597) | ~l1_pre_topc(B_596) | ~v2_pre_topc(B_596) | v2_struct_0(B_596) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595) | v2_struct_0(A_595))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.89/1.64  tff(c_400, plain, (![D_598]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_598))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_598) | ~m1_pre_topc(D_598, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_398])).
% 3.89/1.64  tff(c_403, plain, (![D_598]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_598))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_598) | ~m1_pre_topc(D_598, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_38, c_36, c_400])).
% 3.89/1.64  tff(c_404, plain, (![D_598]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_598))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_598) | ~m1_pre_topc(D_598, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_403])).
% 3.89/1.64  tff(c_456, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_445, c_404])).
% 3.89/1.64  tff(c_463, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_456])).
% 3.89/1.64  tff(c_569, plain, (![B_617, C_614, E_618, D_615, H_616, A_613]: (r1_tmap_1(C_614, B_617, k3_tmap_1(A_613, B_617, k1_tsep_1(A_613, C_614, D_615), C_614, E_618), H_616) | ~r1_tmap_1(k1_tsep_1(A_613, C_614, D_615), B_617, E_618, H_616) | ~m1_subset_1(H_616, u1_struct_0(k1_tsep_1(A_613, C_614, D_615))) | ~m1_subset_1(H_616, u1_struct_0(D_615)) | ~m1_subset_1(H_616, u1_struct_0(C_614)) | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_613, C_614, D_615)), u1_struct_0(B_617)))) | ~v1_funct_2(E_618, u1_struct_0(k1_tsep_1(A_613, C_614, D_615)), u1_struct_0(B_617)) | ~v1_funct_1(E_618) | ~m1_pre_topc(D_615, A_613) | v2_struct_0(D_615) | ~m1_pre_topc(C_614, A_613) | v2_struct_0(C_614) | ~l1_pre_topc(B_617) | ~v2_pre_topc(B_617) | v2_struct_0(B_617) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.89/1.64  tff(c_571, plain, (![B_617, E_618, H_616]: (r1_tmap_1('#skF_4', B_617, k3_tmap_1('#skF_1', B_617, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_618), H_616) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_617, E_618, H_616) | ~m1_subset_1(H_616, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_616, u1_struct_0('#skF_5')) | ~m1_subset_1(H_616, u1_struct_0('#skF_4')) | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_617)))) | ~v1_funct_2(E_618, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_617)) | ~v1_funct_1(E_618) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_617) | ~v2_pre_topc(B_617) | v2_struct_0(B_617) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_569])).
% 3.89/1.64  tff(c_573, plain, (![B_617, E_618, H_616]: (r1_tmap_1('#skF_4', B_617, k3_tmap_1('#skF_1', B_617, '#skF_1', '#skF_4', E_618), H_616) | ~r1_tmap_1('#skF_1', B_617, E_618, H_616) | ~m1_subset_1(H_616, u1_struct_0('#skF_1')) | ~m1_subset_1(H_616, u1_struct_0('#skF_5')) | ~m1_subset_1(H_616, u1_struct_0('#skF_4')) | ~m1_subset_1(E_618, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_617)))) | ~v1_funct_2(E_618, u1_struct_0('#skF_1'), u1_struct_0(B_617)) | ~v1_funct_1(E_618) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_617) | ~v2_pre_topc(B_617) | v2_struct_0(B_617) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_26, c_24, c_24, c_24, c_24, c_571])).
% 3.89/1.64  tff(c_676, plain, (![B_631, E_632, H_633]: (r1_tmap_1('#skF_4', B_631, k3_tmap_1('#skF_1', B_631, '#skF_1', '#skF_4', E_632), H_633) | ~r1_tmap_1('#skF_1', B_631, E_632, H_633) | ~m1_subset_1(H_633, u1_struct_0('#skF_1')) | ~m1_subset_1(H_633, u1_struct_0('#skF_5')) | ~m1_subset_1(H_633, u1_struct_0('#skF_4')) | ~m1_subset_1(E_632, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_631)))) | ~v1_funct_2(E_632, u1_struct_0('#skF_1'), u1_struct_0(B_631)) | ~v1_funct_1(E_632) | ~l1_pre_topc(B_631) | ~v2_pre_topc(B_631) | v2_struct_0(B_631))), inference(negUnitSimplification, [status(thm)], [c_50, c_32, c_28, c_573])).
% 3.89/1.64  tff(c_678, plain, (![H_633]: (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), H_633) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_633) | ~m1_subset_1(H_633, u1_struct_0('#skF_1')) | ~m1_subset_1(H_633, u1_struct_0('#skF_5')) | ~m1_subset_1(H_633, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_676])).
% 3.89/1.64  tff(c_681, plain, (![H_633]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_633) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_633) | ~m1_subset_1(H_633, u1_struct_0('#skF_1')) | ~m1_subset_1(H_633, u1_struct_0('#skF_5')) | ~m1_subset_1(H_633, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_463, c_678])).
% 3.89/1.64  tff(c_683, plain, (![H_634]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_634) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_634) | ~m1_subset_1(H_634, u1_struct_0('#skF_1')) | ~m1_subset_1(H_634, u1_struct_0('#skF_5')) | ~m1_subset_1(H_634, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_681])).
% 3.89/1.64  tff(c_395, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_71])).
% 3.89/1.64  tff(c_686, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_683, c_395])).
% 3.89/1.64  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_18, c_67, c_394, c_686])).
% 3.89/1.64  tff(c_691, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.89/1.64  tff(c_703, plain, (![B_639, D_641, E_640, C_642, A_643]: (k3_tmap_1(A_643, B_639, C_642, D_641, E_640)=k2_partfun1(u1_struct_0(C_642), u1_struct_0(B_639), E_640, u1_struct_0(D_641)) | ~m1_pre_topc(D_641, C_642) | ~m1_subset_1(E_640, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_642), u1_struct_0(B_639)))) | ~v1_funct_2(E_640, u1_struct_0(C_642), u1_struct_0(B_639)) | ~v1_funct_1(E_640) | ~m1_pre_topc(D_641, A_643) | ~m1_pre_topc(C_642, A_643) | ~l1_pre_topc(B_639) | ~v2_pre_topc(B_639) | v2_struct_0(B_639) | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.89/1.64  tff(c_705, plain, (![A_643, D_641]: (k3_tmap_1(A_643, '#skF_2', '#skF_1', D_641, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_641)) | ~m1_pre_topc(D_641, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_641, A_643) | ~m1_pre_topc('#skF_1', A_643) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(resolution, [status(thm)], [c_34, c_703])).
% 3.89/1.64  tff(c_708, plain, (![A_643, D_641]: (k3_tmap_1(A_643, '#skF_2', '#skF_1', D_641, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_641)) | ~m1_pre_topc(D_641, '#skF_1') | ~m1_pre_topc(D_641, A_643) | ~m1_pre_topc('#skF_1', A_643) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_705])).
% 3.89/1.64  tff(c_719, plain, (![A_645, D_646]: (k3_tmap_1(A_645, '#skF_2', '#skF_1', D_646, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_646)) | ~m1_pre_topc(D_646, '#skF_1') | ~m1_pre_topc(D_646, A_645) | ~m1_pre_topc('#skF_1', A_645) | ~l1_pre_topc(A_645) | ~v2_pre_topc(A_645) | v2_struct_0(A_645))), inference(negUnitSimplification, [status(thm)], [c_44, c_708])).
% 3.89/1.64  tff(c_723, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_719])).
% 3.89/1.64  tff(c_729, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_723])).
% 3.89/1.64  tff(c_730, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_729])).
% 3.89/1.64  tff(c_735, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_730])).
% 3.89/1.64  tff(c_739, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_735])).
% 3.89/1.64  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_739])).
% 3.89/1.64  tff(c_745, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_730])).
% 3.89/1.64  tff(c_725, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_719])).
% 3.89/1.64  tff(c_733, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_26, c_725])).
% 3.89/1.64  tff(c_734, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_733])).
% 3.89/1.64  tff(c_814, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_745, c_734])).
% 3.89/1.64  tff(c_696, plain, (![A_635, B_636, C_637, D_638]: (k2_partfun1(u1_struct_0(A_635), u1_struct_0(B_636), C_637, u1_struct_0(D_638))=k2_tmap_1(A_635, B_636, C_637, D_638) | ~m1_pre_topc(D_638, A_635) | ~m1_subset_1(C_637, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_635), u1_struct_0(B_636)))) | ~v1_funct_2(C_637, u1_struct_0(A_635), u1_struct_0(B_636)) | ~v1_funct_1(C_637) | ~l1_pre_topc(B_636) | ~v2_pre_topc(B_636) | v2_struct_0(B_636) | ~l1_pre_topc(A_635) | ~v2_pre_topc(A_635) | v2_struct_0(A_635))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.89/1.64  tff(c_698, plain, (![D_638]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_638))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_638) | ~m1_pre_topc(D_638, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_696])).
% 3.89/1.64  tff(c_701, plain, (![D_638]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_638))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_638) | ~m1_pre_topc(D_638, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_38, c_36, c_698])).
% 3.89/1.64  tff(c_702, plain, (![D_638]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_638))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_638) | ~m1_pre_topc(D_638, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_701])).
% 3.89/1.64  tff(c_818, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_814, c_702])).
% 3.89/1.64  tff(c_825, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_818])).
% 3.89/1.64  tff(c_868, plain, (![D_655, A_653, C_654, H_656, E_658, B_657]: (r1_tmap_1(D_655, B_657, k3_tmap_1(A_653, B_657, k1_tsep_1(A_653, C_654, D_655), D_655, E_658), H_656) | ~r1_tmap_1(k1_tsep_1(A_653, C_654, D_655), B_657, E_658, H_656) | ~m1_subset_1(H_656, u1_struct_0(k1_tsep_1(A_653, C_654, D_655))) | ~m1_subset_1(H_656, u1_struct_0(D_655)) | ~m1_subset_1(H_656, u1_struct_0(C_654)) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_653, C_654, D_655)), u1_struct_0(B_657)))) | ~v1_funct_2(E_658, u1_struct_0(k1_tsep_1(A_653, C_654, D_655)), u1_struct_0(B_657)) | ~v1_funct_1(E_658) | ~m1_pre_topc(D_655, A_653) | v2_struct_0(D_655) | ~m1_pre_topc(C_654, A_653) | v2_struct_0(C_654) | ~l1_pre_topc(B_657) | ~v2_pre_topc(B_657) | v2_struct_0(B_657) | ~l1_pre_topc(A_653) | ~v2_pre_topc(A_653) | v2_struct_0(A_653))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.89/1.64  tff(c_870, plain, (![B_657, E_658, H_656]: (r1_tmap_1('#skF_5', B_657, k3_tmap_1('#skF_1', B_657, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_658), H_656) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_657, E_658, H_656) | ~m1_subset_1(H_656, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_656, u1_struct_0('#skF_5')) | ~m1_subset_1(H_656, u1_struct_0('#skF_4')) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_657)))) | ~v1_funct_2(E_658, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_657)) | ~v1_funct_1(E_658) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_657) | ~v2_pre_topc(B_657) | v2_struct_0(B_657) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_868])).
% 3.89/1.64  tff(c_872, plain, (![B_657, E_658, H_656]: (r1_tmap_1('#skF_5', B_657, k3_tmap_1('#skF_1', B_657, '#skF_1', '#skF_5', E_658), H_656) | ~r1_tmap_1('#skF_1', B_657, E_658, H_656) | ~m1_subset_1(H_656, u1_struct_0('#skF_1')) | ~m1_subset_1(H_656, u1_struct_0('#skF_5')) | ~m1_subset_1(H_656, u1_struct_0('#skF_4')) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_657)))) | ~v1_funct_2(E_658, u1_struct_0('#skF_1'), u1_struct_0(B_657)) | ~v1_funct_1(E_658) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_657) | ~v2_pre_topc(B_657) | v2_struct_0(B_657) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_30, c_26, c_24, c_24, c_24, c_24, c_870])).
% 3.89/1.64  tff(c_975, plain, (![B_671, E_672, H_673]: (r1_tmap_1('#skF_5', B_671, k3_tmap_1('#skF_1', B_671, '#skF_1', '#skF_5', E_672), H_673) | ~r1_tmap_1('#skF_1', B_671, E_672, H_673) | ~m1_subset_1(H_673, u1_struct_0('#skF_1')) | ~m1_subset_1(H_673, u1_struct_0('#skF_5')) | ~m1_subset_1(H_673, u1_struct_0('#skF_4')) | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_671)))) | ~v1_funct_2(E_672, u1_struct_0('#skF_1'), u1_struct_0(B_671)) | ~v1_funct_1(E_672) | ~l1_pre_topc(B_671) | ~v2_pre_topc(B_671) | v2_struct_0(B_671))), inference(negUnitSimplification, [status(thm)], [c_50, c_32, c_28, c_872])).
% 3.89/1.64  tff(c_977, plain, (![H_673]: (r1_tmap_1('#skF_5', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), H_673) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_673) | ~m1_subset_1(H_673, u1_struct_0('#skF_1')) | ~m1_subset_1(H_673, u1_struct_0('#skF_5')) | ~m1_subset_1(H_673, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_975])).
% 3.89/1.64  tff(c_980, plain, (![H_673]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_673) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_673) | ~m1_subset_1(H_673, u1_struct_0('#skF_1')) | ~m1_subset_1(H_673, u1_struct_0('#skF_5')) | ~m1_subset_1(H_673, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_825, c_977])).
% 3.89/1.64  tff(c_982, plain, (![H_674]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_674) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_674) | ~m1_subset_1(H_674, u1_struct_0('#skF_1')) | ~m1_subset_1(H_674, u1_struct_0('#skF_5')) | ~m1_subset_1(H_674, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_980])).
% 3.89/1.64  tff(c_692, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.89/1.64  tff(c_985, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_982, c_692])).
% 3.89/1.64  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_18, c_67, c_691, c_985])).
% 3.89/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.64  
% 3.89/1.64  Inference rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Ref     : 0
% 3.89/1.64  #Sup     : 191
% 3.89/1.64  #Fact    : 0
% 3.89/1.64  #Define  : 0
% 3.89/1.64  #Split   : 12
% 3.89/1.64  #Chain   : 0
% 3.89/1.64  #Close   : 0
% 3.89/1.64  
% 3.89/1.64  Ordering : KBO
% 3.89/1.64  
% 3.89/1.64  Simplification rules
% 3.89/1.64  ----------------------
% 3.89/1.64  #Subsume      : 17
% 3.89/1.64  #Demod        : 329
% 3.89/1.64  #Tautology    : 122
% 3.89/1.64  #SimpNegUnit  : 62
% 3.89/1.64  #BackRed      : 9
% 3.89/1.64  
% 3.89/1.64  #Partial instantiations: 0
% 3.89/1.64  #Strategies tried      : 1
% 3.89/1.64  
% 3.89/1.64  Timing (in seconds)
% 3.89/1.64  ----------------------
% 3.89/1.64  Preprocessing        : 0.37
% 3.89/1.64  Parsing              : 0.17
% 3.89/1.64  CNF conversion       : 0.07
% 3.89/1.64  Main loop            : 0.43
% 3.89/1.64  Inferencing          : 0.15
% 3.89/1.64  Reduction            : 0.15
% 3.89/1.64  Demodulation         : 0.11
% 3.89/1.64  BG Simplification    : 0.02
% 3.89/1.64  Subsumption          : 0.07
% 3.89/1.64  Abstraction          : 0.02
% 3.89/1.64  MUC search           : 0.00
% 3.89/1.64  Cooper               : 0.00
% 3.89/1.64  Total                : 0.86
% 3.89/1.64  Index Insertion      : 0.00
% 3.89/1.64  Index Deletion       : 0.00
% 3.89/1.64  Index Matching       : 0.00
% 3.89/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
