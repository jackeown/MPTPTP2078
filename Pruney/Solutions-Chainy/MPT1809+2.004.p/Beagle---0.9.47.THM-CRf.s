%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:05 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 596 expanded)
%              Number of leaves         :   32 ( 255 expanded)
%              Depth                    :   15
%              Number of atoms          :  701 (5815 expanded)
%              Number of equality atoms :   54 ( 753 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_215,negated_conjecture,(
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

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_159,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_tmap_1)).

tff(c_18,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_20,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_74,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_22,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_69])).

tff(c_89,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_62])).

tff(c_88,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_56,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_67,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_56])).

tff(c_73,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_67])).

tff(c_112,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88,c_73])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_30,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_28,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_104,plain,(
    ! [A_558,B_559,C_560] :
      ( m1_pre_topc(k1_tsep_1(A_558,B_559,C_560),A_558)
      | ~ m1_pre_topc(C_560,A_558)
      | v2_struct_0(C_560)
      | ~ m1_pre_topc(B_559,A_558)
      | v2_struct_0(B_559)
      | ~ l1_pre_topc(A_558)
      | v2_struct_0(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_107,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_109,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_30,c_107])).

tff(c_110,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_109])).

tff(c_129,plain,(
    ! [C_569,D_568,A_570,E_567,B_566] :
      ( k3_tmap_1(A_570,B_566,C_569,D_568,E_567) = k2_partfun1(u1_struct_0(C_569),u1_struct_0(B_566),E_567,u1_struct_0(D_568))
      | ~ m1_pre_topc(D_568,C_569)
      | ~ m1_subset_1(E_567,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_569),u1_struct_0(B_566))))
      | ~ v1_funct_2(E_567,u1_struct_0(C_569),u1_struct_0(B_566))
      | ~ v1_funct_1(E_567)
      | ~ m1_pre_topc(D_568,A_570)
      | ~ m1_pre_topc(C_569,A_570)
      | ~ l1_pre_topc(B_566)
      | ~ v2_pre_topc(B_566)
      | v2_struct_0(B_566)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [A_570,D_568] :
      ( k3_tmap_1(A_570,'#skF_2','#skF_1',D_568,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_568))
      | ~ m1_pre_topc(D_568,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_568,A_570)
      | ~ m1_pre_topc('#skF_1',A_570)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_134,plain,(
    ! [A_570,D_568] :
      ( k3_tmap_1(A_570,'#skF_2','#skF_1',D_568,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_568))
      | ~ m1_pre_topc(D_568,'#skF_1')
      | ~ m1_pre_topc(D_568,A_570)
      | ~ m1_pre_topc('#skF_1',A_570)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_131])).

tff(c_136,plain,(
    ! [A_571,D_572] :
      ( k3_tmap_1(A_571,'#skF_2','#skF_1',D_572,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_572))
      | ~ m1_pre_topc(D_572,'#skF_1')
      | ~ m1_pre_topc(D_572,A_571)
      | ~ m1_pre_topc('#skF_1',A_571)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_134])).

tff(c_144,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_156,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_110,c_34,c_144])).

tff(c_157,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_156])).

tff(c_113,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k2_partfun1(u1_struct_0(A_561),u1_struct_0(B_562),C_563,u1_struct_0(D_564)) = k2_tmap_1(A_561,B_562,C_563,D_564)
      | ~ m1_pre_topc(D_564,A_561)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561),u1_struct_0(B_562))))
      | ~ v1_funct_2(C_563,u1_struct_0(A_561),u1_struct_0(B_562))
      | ~ v1_funct_1(C_563)
      | ~ l1_pre_topc(B_562)
      | ~ v2_pre_topc(B_562)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_564)
      | ~ m1_pre_topc(D_564,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_118,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_564)
      | ~ m1_pre_topc(D_564,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_42,c_40,c_115])).

tff(c_119,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_564)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_564)
      | ~ m1_pre_topc(D_564,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_118])).

tff(c_203,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_119])).

tff(c_210,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_203])).

tff(c_142,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_152,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_110,c_30,c_142])).

tff(c_153,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_152])).

tff(c_221,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_153])).

tff(c_227,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_221])).

tff(c_365,plain,(
    ! [B_606,E_604,D_607,H_603,A_602,C_605] :
      ( r1_tmap_1(k1_tsep_1(A_602,C_605,D_607),B_606,E_604,H_603)
      | ~ r1_tmap_1(D_607,B_606,k3_tmap_1(A_602,B_606,k1_tsep_1(A_602,C_605,D_607),D_607,E_604),H_603)
      | ~ r1_tmap_1(C_605,B_606,k3_tmap_1(A_602,B_606,k1_tsep_1(A_602,C_605,D_607),C_605,E_604),H_603)
      | ~ m1_subset_1(H_603,u1_struct_0(k1_tsep_1(A_602,C_605,D_607)))
      | ~ m1_subset_1(H_603,u1_struct_0(D_607))
      | ~ m1_subset_1(H_603,u1_struct_0(C_605))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_602,C_605,D_607)),u1_struct_0(B_606))))
      | ~ v1_funct_2(E_604,u1_struct_0(k1_tsep_1(A_602,C_605,D_607)),u1_struct_0(B_606))
      | ~ v1_funct_1(E_604)
      | ~ m1_pre_topc(D_607,A_602)
      | v2_struct_0(D_607)
      | ~ m1_pre_topc(C_605,A_602)
      | v2_struct_0(C_605)
      | ~ l1_pre_topc(B_606)
      | ~ v2_pre_topc(B_606)
      | v2_struct_0(B_606)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_367,plain,(
    ! [B_606,E_604,H_603] :
      ( r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_606,E_604,H_603)
      | ~ r1_tmap_1('#skF_5',B_606,k3_tmap_1('#skF_1',B_606,'#skF_1','#skF_5',E_604),H_603)
      | ~ r1_tmap_1('#skF_4',B_606,k3_tmap_1('#skF_1',B_606,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_604),H_603)
      | ~ m1_subset_1(H_603,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_603,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_603,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_606))))
      | ~ v1_funct_2(E_604,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_606))
      | ~ v1_funct_1(E_604)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_606)
      | ~ v2_pre_topc(B_606)
      | v2_struct_0(B_606)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_365])).

tff(c_369,plain,(
    ! [B_606,E_604,H_603] :
      ( r1_tmap_1('#skF_1',B_606,E_604,H_603)
      | ~ r1_tmap_1('#skF_5',B_606,k3_tmap_1('#skF_1',B_606,'#skF_1','#skF_5',E_604),H_603)
      | ~ r1_tmap_1('#skF_4',B_606,k3_tmap_1('#skF_1',B_606,'#skF_1','#skF_4',E_604),H_603)
      | ~ m1_subset_1(H_603,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_603,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_603,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_606))))
      | ~ v1_funct_2(E_604,u1_struct_0('#skF_1'),u1_struct_0(B_606))
      | ~ v1_funct_1(E_604)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_606)
      | ~ v2_pre_topc(B_606)
      | v2_struct_0(B_606)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_34,c_30,c_28,c_28,c_28,c_28,c_28,c_367])).

tff(c_372,plain,(
    ! [B_609,E_610,H_611] :
      ( r1_tmap_1('#skF_1',B_609,E_610,H_611)
      | ~ r1_tmap_1('#skF_5',B_609,k3_tmap_1('#skF_1',B_609,'#skF_1','#skF_5',E_610),H_611)
      | ~ r1_tmap_1('#skF_4',B_609,k3_tmap_1('#skF_1',B_609,'#skF_1','#skF_4',E_610),H_611)
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_609))))
      | ~ v1_funct_2(E_610,u1_struct_0('#skF_1'),u1_struct_0(B_609))
      | ~ v1_funct_1(E_610)
      | ~ l1_pre_topc(B_609)
      | ~ v2_pre_topc(B_609)
      | v2_struct_0(B_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_369])).

tff(c_374,plain,(
    ! [H_611] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_611)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_611)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),H_611)
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_372])).

tff(c_376,plain,(
    ! [H_611] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_611)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_611)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_611)
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_611,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_210,c_374])).

tff(c_378,plain,(
    ! [H_612] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_612)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_612)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_612)
      | ~ m1_subset_1(H_612,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_612,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_612,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_376])).

tff(c_384,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_378])).

tff(c_388,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22,c_71,c_89,c_384])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_388])).

tff(c_391,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_415,plain,(
    ! [A_619,B_620,C_621] :
      ( m1_pre_topc(k1_tsep_1(A_619,B_620,C_621),A_619)
      | ~ m1_pre_topc(C_621,A_619)
      | v2_struct_0(C_621)
      | ~ m1_pre_topc(B_620,A_619)
      | v2_struct_0(B_620)
      | ~ l1_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_418,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_415])).

tff(c_420,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_30,c_418])).

tff(c_421,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_420])).

tff(c_438,plain,(
    ! [C_630,B_627,E_628,A_631,D_629] :
      ( k3_tmap_1(A_631,B_627,C_630,D_629,E_628) = k2_partfun1(u1_struct_0(C_630),u1_struct_0(B_627),E_628,u1_struct_0(D_629))
      | ~ m1_pre_topc(D_629,C_630)
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_630),u1_struct_0(B_627))))
      | ~ v1_funct_2(E_628,u1_struct_0(C_630),u1_struct_0(B_627))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc(D_629,A_631)
      | ~ m1_pre_topc(C_630,A_631)
      | ~ l1_pre_topc(B_627)
      | ~ v2_pre_topc(B_627)
      | v2_struct_0(B_627)
      | ~ l1_pre_topc(A_631)
      | ~ v2_pre_topc(A_631)
      | v2_struct_0(A_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_440,plain,(
    ! [A_631,D_629] :
      ( k3_tmap_1(A_631,'#skF_2','#skF_1',D_629,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_629))
      | ~ m1_pre_topc(D_629,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_629,A_631)
      | ~ m1_pre_topc('#skF_1',A_631)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_631)
      | ~ v2_pre_topc(A_631)
      | v2_struct_0(A_631) ) ),
    inference(resolution,[status(thm)],[c_38,c_438])).

tff(c_443,plain,(
    ! [A_631,D_629] :
      ( k3_tmap_1(A_631,'#skF_2','#skF_1',D_629,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_629))
      | ~ m1_pre_topc(D_629,'#skF_1')
      | ~ m1_pre_topc(D_629,A_631)
      | ~ m1_pre_topc('#skF_1',A_631)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_631)
      | ~ v2_pre_topc(A_631)
      | v2_struct_0(A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_440])).

tff(c_445,plain,(
    ! [A_632,D_633] :
      ( k3_tmap_1(A_632,'#skF_2','#skF_1',D_633,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_633))
      | ~ m1_pre_topc(D_633,'#skF_1')
      | ~ m1_pre_topc(D_633,A_632)
      | ~ m1_pre_topc('#skF_1',A_632)
      | ~ l1_pre_topc(A_632)
      | ~ v2_pre_topc(A_632)
      | v2_struct_0(A_632) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_443])).

tff(c_453,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_445])).

tff(c_465,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_421,c_34,c_453])).

tff(c_466,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_465])).

tff(c_422,plain,(
    ! [A_622,B_623,C_624,D_625] :
      ( k2_partfun1(u1_struct_0(A_622),u1_struct_0(B_623),C_624,u1_struct_0(D_625)) = k2_tmap_1(A_622,B_623,C_624,D_625)
      | ~ m1_pre_topc(D_625,A_622)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_622),u1_struct_0(B_623))))
      | ~ v1_funct_2(C_624,u1_struct_0(A_622),u1_struct_0(B_623))
      | ~ v1_funct_1(C_624)
      | ~ l1_pre_topc(B_623)
      | ~ v2_pre_topc(B_623)
      | v2_struct_0(B_623)
      | ~ l1_pre_topc(A_622)
      | ~ v2_pre_topc(A_622)
      | v2_struct_0(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_424,plain,(
    ! [D_625] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_625)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_625)
      | ~ m1_pre_topc(D_625,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_422])).

tff(c_427,plain,(
    ! [D_625] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_625)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_625)
      | ~ m1_pre_topc(D_625,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_42,c_40,c_424])).

tff(c_428,plain,(
    ! [D_625] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_625)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_625)
      | ~ m1_pre_topc(D_625,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_427])).

tff(c_496,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_428])).

tff(c_503,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_496])).

tff(c_467,plain,(
    ! [A_634,B_638,E_636,C_637,D_639,H_635] :
      ( r1_tmap_1(C_637,B_638,k3_tmap_1(A_634,B_638,k1_tsep_1(A_634,C_637,D_639),C_637,E_636),H_635)
      | ~ r1_tmap_1(k1_tsep_1(A_634,C_637,D_639),B_638,E_636,H_635)
      | ~ m1_subset_1(H_635,u1_struct_0(k1_tsep_1(A_634,C_637,D_639)))
      | ~ m1_subset_1(H_635,u1_struct_0(D_639))
      | ~ m1_subset_1(H_635,u1_struct_0(C_637))
      | ~ m1_subset_1(E_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_634,C_637,D_639)),u1_struct_0(B_638))))
      | ~ v1_funct_2(E_636,u1_struct_0(k1_tsep_1(A_634,C_637,D_639)),u1_struct_0(B_638))
      | ~ v1_funct_1(E_636)
      | ~ m1_pre_topc(D_639,A_634)
      | v2_struct_0(D_639)
      | ~ m1_pre_topc(C_637,A_634)
      | v2_struct_0(C_637)
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638)
      | ~ l1_pre_topc(A_634)
      | ~ v2_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_469,plain,(
    ! [B_638,E_636,H_635] :
      ( r1_tmap_1('#skF_4',B_638,k3_tmap_1('#skF_1',B_638,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_4',E_636),H_635)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_638,E_636,H_635)
      | ~ m1_subset_1(H_635,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_635,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_635,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_638))))
      | ~ v1_funct_2(E_636,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_638))
      | ~ v1_funct_1(E_636)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_467])).

tff(c_471,plain,(
    ! [B_638,E_636,H_635] :
      ( r1_tmap_1('#skF_4',B_638,k3_tmap_1('#skF_1',B_638,'#skF_1','#skF_4',E_636),H_635)
      | ~ r1_tmap_1('#skF_1',B_638,E_636,H_635)
      | ~ m1_subset_1(H_635,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_635,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_635,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_638))))
      | ~ v1_funct_2(E_636,u1_struct_0('#skF_1'),u1_struct_0(B_638))
      | ~ v1_funct_1(E_636)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_638)
      | ~ v2_pre_topc(B_638)
      | v2_struct_0(B_638)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_34,c_30,c_28,c_28,c_28,c_28,c_469])).

tff(c_673,plain,(
    ! [B_666,E_667,H_668] :
      ( r1_tmap_1('#skF_4',B_666,k3_tmap_1('#skF_1',B_666,'#skF_1','#skF_4',E_667),H_668)
      | ~ r1_tmap_1('#skF_1',B_666,E_667,H_668)
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_667,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_666))))
      | ~ v1_funct_2(E_667,u1_struct_0('#skF_1'),u1_struct_0(B_666))
      | ~ v1_funct_1(E_667)
      | ~ l1_pre_topc(B_666)
      | ~ v2_pre_topc(B_666)
      | v2_struct_0(B_666) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_471])).

tff(c_675,plain,(
    ! [H_668] :
      ( r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3'),H_668)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_668)
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_673])).

tff(c_678,plain,(
    ! [H_668] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_668)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_668)
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_668,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_503,c_675])).

tff(c_680,plain,(
    ! [H_669] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_669)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_669)
      | ~ m1_subset_1(H_669,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_669,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_669,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_678])).

tff(c_392,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_683,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_680,c_392])).

tff(c_687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22,c_71,c_391,c_683])).

tff(c_688,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_714,plain,(
    ! [A_679,B_680,C_681,D_682] :
      ( k2_partfun1(u1_struct_0(A_679),u1_struct_0(B_680),C_681,u1_struct_0(D_682)) = k2_tmap_1(A_679,B_680,C_681,D_682)
      | ~ m1_pre_topc(D_682,A_679)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_679),u1_struct_0(B_680))))
      | ~ v1_funct_2(C_681,u1_struct_0(A_679),u1_struct_0(B_680))
      | ~ v1_funct_1(C_681)
      | ~ l1_pre_topc(B_680)
      | ~ v2_pre_topc(B_680)
      | v2_struct_0(B_680)
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679)
      | v2_struct_0(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_716,plain,(
    ! [D_682] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_682)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_682)
      | ~ m1_pre_topc(D_682,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_714])).

tff(c_719,plain,(
    ! [D_682] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_682)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_682)
      | ~ m1_pre_topc(D_682,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_42,c_40,c_716])).

tff(c_720,plain,(
    ! [D_682] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_682)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_682)
      | ~ m1_pre_topc(D_682,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_719])).

tff(c_705,plain,(
    ! [A_676,B_677,C_678] :
      ( m1_pre_topc(k1_tsep_1(A_676,B_677,C_678),A_676)
      | ~ m1_pre_topc(C_678,A_676)
      | v2_struct_0(C_678)
      | ~ m1_pre_topc(B_677,A_676)
      | v2_struct_0(B_677)
      | ~ l1_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_708,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_705])).

tff(c_710,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_34,c_30,c_708])).

tff(c_711,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_710])).

tff(c_730,plain,(
    ! [B_684,E_685,D_686,A_688,C_687] :
      ( k3_tmap_1(A_688,B_684,C_687,D_686,E_685) = k2_partfun1(u1_struct_0(C_687),u1_struct_0(B_684),E_685,u1_struct_0(D_686))
      | ~ m1_pre_topc(D_686,C_687)
      | ~ m1_subset_1(E_685,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_687),u1_struct_0(B_684))))
      | ~ v1_funct_2(E_685,u1_struct_0(C_687),u1_struct_0(B_684))
      | ~ v1_funct_1(E_685)
      | ~ m1_pre_topc(D_686,A_688)
      | ~ m1_pre_topc(C_687,A_688)
      | ~ l1_pre_topc(B_684)
      | ~ v2_pre_topc(B_684)
      | v2_struct_0(B_684)
      | ~ l1_pre_topc(A_688)
      | ~ v2_pre_topc(A_688)
      | v2_struct_0(A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_732,plain,(
    ! [A_688,D_686] :
      ( k3_tmap_1(A_688,'#skF_2','#skF_1',D_686,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_686))
      | ~ m1_pre_topc(D_686,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_686,A_688)
      | ~ m1_pre_topc('#skF_1',A_688)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_688)
      | ~ v2_pre_topc(A_688)
      | v2_struct_0(A_688) ) ),
    inference(resolution,[status(thm)],[c_38,c_730])).

tff(c_735,plain,(
    ! [A_688,D_686] :
      ( k3_tmap_1(A_688,'#skF_2','#skF_1',D_686,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_686))
      | ~ m1_pre_topc(D_686,'#skF_1')
      | ~ m1_pre_topc(D_686,A_688)
      | ~ m1_pre_topc('#skF_1',A_688)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_688)
      | ~ v2_pre_topc(A_688)
      | v2_struct_0(A_688) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_732])).

tff(c_737,plain,(
    ! [A_689,D_690] :
      ( k3_tmap_1(A_689,'#skF_2','#skF_1',D_690,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_690))
      | ~ m1_pre_topc(D_690,'#skF_1')
      | ~ m1_pre_topc(D_690,A_689)
      | ~ m1_pre_topc('#skF_1',A_689)
      | ~ l1_pre_topc(A_689)
      | ~ v2_pre_topc(A_689)
      | v2_struct_0(A_689) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_735])).

tff(c_743,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_737])).

tff(c_753,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_711,c_30,c_743])).

tff(c_754,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_753])).

tff(c_827,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_754])).

tff(c_833,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_827])).

tff(c_873,plain,(
    ! [E_699,A_697,H_698,B_701,C_700,D_702] :
      ( r1_tmap_1(D_702,B_701,k3_tmap_1(A_697,B_701,k1_tsep_1(A_697,C_700,D_702),D_702,E_699),H_698)
      | ~ r1_tmap_1(k1_tsep_1(A_697,C_700,D_702),B_701,E_699,H_698)
      | ~ m1_subset_1(H_698,u1_struct_0(k1_tsep_1(A_697,C_700,D_702)))
      | ~ m1_subset_1(H_698,u1_struct_0(D_702))
      | ~ m1_subset_1(H_698,u1_struct_0(C_700))
      | ~ m1_subset_1(E_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_697,C_700,D_702)),u1_struct_0(B_701))))
      | ~ v1_funct_2(E_699,u1_struct_0(k1_tsep_1(A_697,C_700,D_702)),u1_struct_0(B_701))
      | ~ v1_funct_1(E_699)
      | ~ m1_pre_topc(D_702,A_697)
      | v2_struct_0(D_702)
      | ~ m1_pre_topc(C_700,A_697)
      | v2_struct_0(C_700)
      | ~ l1_pre_topc(B_701)
      | ~ v2_pre_topc(B_701)
      | v2_struct_0(B_701)
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_875,plain,(
    ! [B_701,E_699,H_698] :
      ( r1_tmap_1('#skF_5',B_701,k3_tmap_1('#skF_1',B_701,k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_5',E_699),H_698)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_701,E_699,H_698)
      | ~ m1_subset_1(H_698,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_subset_1(H_698,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_698,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_701))))
      | ~ v1_funct_2(E_699,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(B_701))
      | ~ v1_funct_1(E_699)
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_701)
      | ~ v2_pre_topc(B_701)
      | v2_struct_0(B_701)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_873])).

tff(c_877,plain,(
    ! [B_701,E_699,H_698] :
      ( r1_tmap_1('#skF_5',B_701,k3_tmap_1('#skF_1',B_701,'#skF_1','#skF_5',E_699),H_698)
      | ~ r1_tmap_1('#skF_1',B_701,E_699,H_698)
      | ~ m1_subset_1(H_698,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_698,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_698,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_701))))
      | ~ v1_funct_2(E_699,u1_struct_0('#skF_1'),u1_struct_0(B_701))
      | ~ v1_funct_1(E_699)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_701)
      | ~ v2_pre_topc(B_701)
      | v2_struct_0(B_701)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_34,c_30,c_28,c_28,c_28,c_28,c_875])).

tff(c_959,plain,(
    ! [B_717,E_718,H_719] :
      ( r1_tmap_1('#skF_5',B_717,k3_tmap_1('#skF_1',B_717,'#skF_1','#skF_5',E_718),H_719)
      | ~ r1_tmap_1('#skF_1',B_717,E_718,H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_717))))
      | ~ v1_funct_2(E_718,u1_struct_0('#skF_1'),u1_struct_0(B_717))
      | ~ v1_funct_1(E_718)
      | ~ l1_pre_topc(B_717)
      | ~ v2_pre_topc(B_717)
      | v2_struct_0(B_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_36,c_32,c_877])).

tff(c_961,plain,(
    ! [H_719] :
      ( r1_tmap_1('#skF_5','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_5','#skF_3'),H_719)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_959])).

tff(c_964,plain,(
    ! [H_719] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_719)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_833,c_961])).

tff(c_966,plain,(
    ! [H_720] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_720)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_720)
      | ~ m1_subset_1(H_720,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(H_720,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_720,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_964])).

tff(c_689,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_969,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_966,c_689])).

tff(c_973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_22,c_71,c_688,c_969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.60  
% 3.80/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.61  %$ r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.80/1.61  
% 3.80/1.61  %Foreground sorts:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Background operators:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Foreground operators:
% 3.80/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.61  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.80/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.80/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.80/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.80/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.80/1.61  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.80/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.80/1.61  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.80/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.61  
% 3.80/1.63  tff(f_215, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 3.80/1.63  tff(f_106, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.80/1.63  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.80/1.63  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.80/1.63  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(k1_tsep_1(A, C, D))) => (((H = F) & (H = G)) => (r1_tmap_1(k1_tsep_1(A, C, D), B, E, H) <=> (r1_tmap_1(C, B, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), F) & r1_tmap_1(D, B, k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), G)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_tmap_1)).
% 3.80/1.63  tff(c_18, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_20, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_68, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.80/1.63  tff(c_74, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 3.80/1.63  tff(c_22, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_26, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26])).
% 3.80/1.63  tff(c_66, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_69, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 3.80/1.63  tff(c_75, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_69])).
% 3.80/1.63  tff(c_89, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_75])).
% 3.80/1.63  tff(c_62, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_70, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_62])).
% 3.80/1.63  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_70])).
% 3.80/1.63  tff(c_56, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_67, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_56])).
% 3.80/1.63  tff(c_73, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_67])).
% 3.80/1.63  tff(c_112, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88, c_73])).
% 3.80/1.63  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_32, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_30, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_28, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.80/1.63  tff(c_104, plain, (![A_558, B_559, C_560]: (m1_pre_topc(k1_tsep_1(A_558, B_559, C_560), A_558) | ~m1_pre_topc(C_560, A_558) | v2_struct_0(C_560) | ~m1_pre_topc(B_559, A_558) | v2_struct_0(B_559) | ~l1_pre_topc(A_558) | v2_struct_0(A_558))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.80/1.63  tff(c_107, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_104])).
% 3.80/1.63  tff(c_109, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34, c_30, c_107])).
% 3.80/1.63  tff(c_110, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_109])).
% 3.80/1.63  tff(c_129, plain, (![C_569, D_568, A_570, E_567, B_566]: (k3_tmap_1(A_570, B_566, C_569, D_568, E_567)=k2_partfun1(u1_struct_0(C_569), u1_struct_0(B_566), E_567, u1_struct_0(D_568)) | ~m1_pre_topc(D_568, C_569) | ~m1_subset_1(E_567, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_569), u1_struct_0(B_566)))) | ~v1_funct_2(E_567, u1_struct_0(C_569), u1_struct_0(B_566)) | ~v1_funct_1(E_567) | ~m1_pre_topc(D_568, A_570) | ~m1_pre_topc(C_569, A_570) | ~l1_pre_topc(B_566) | ~v2_pre_topc(B_566) | v2_struct_0(B_566) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.80/1.63  tff(c_131, plain, (![A_570, D_568]: (k3_tmap_1(A_570, '#skF_2', '#skF_1', D_568, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_568)) | ~m1_pre_topc(D_568, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_568, A_570) | ~m1_pre_topc('#skF_1', A_570) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(resolution, [status(thm)], [c_38, c_129])).
% 3.80/1.63  tff(c_134, plain, (![A_570, D_568]: (k3_tmap_1(A_570, '#skF_2', '#skF_1', D_568, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_568)) | ~m1_pre_topc(D_568, '#skF_1') | ~m1_pre_topc(D_568, A_570) | ~m1_pre_topc('#skF_1', A_570) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_131])).
% 3.80/1.63  tff(c_136, plain, (![A_571, D_572]: (k3_tmap_1(A_571, '#skF_2', '#skF_1', D_572, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_572)) | ~m1_pre_topc(D_572, '#skF_1') | ~m1_pre_topc(D_572, A_571) | ~m1_pre_topc('#skF_1', A_571) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(negUnitSimplification, [status(thm)], [c_48, c_134])).
% 3.80/1.63  tff(c_144, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_136])).
% 3.80/1.63  tff(c_156, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_110, c_34, c_144])).
% 3.80/1.63  tff(c_157, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_156])).
% 3.80/1.63  tff(c_113, plain, (![A_561, B_562, C_563, D_564]: (k2_partfun1(u1_struct_0(A_561), u1_struct_0(B_562), C_563, u1_struct_0(D_564))=k2_tmap_1(A_561, B_562, C_563, D_564) | ~m1_pre_topc(D_564, A_561) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561), u1_struct_0(B_562)))) | ~v1_funct_2(C_563, u1_struct_0(A_561), u1_struct_0(B_562)) | ~v1_funct_1(C_563) | ~l1_pre_topc(B_562) | ~v2_pre_topc(B_562) | v2_struct_0(B_562) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.80/1.63  tff(c_115, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_564) | ~m1_pre_topc(D_564, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_113])).
% 3.80/1.63  tff(c_118, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_564) | ~m1_pre_topc(D_564, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_42, c_40, c_115])).
% 3.80/1.63  tff(c_119, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_564))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_564) | ~m1_pre_topc(D_564, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_118])).
% 3.80/1.63  tff(c_203, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_157, c_119])).
% 3.80/1.63  tff(c_210, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_203])).
% 3.80/1.63  tff(c_142, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_136])).
% 3.80/1.63  tff(c_152, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_110, c_30, c_142])).
% 3.80/1.63  tff(c_153, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_152])).
% 3.80/1.63  tff(c_221, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_119, c_153])).
% 3.80/1.63  tff(c_227, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_221])).
% 3.80/1.63  tff(c_365, plain, (![B_606, E_604, D_607, H_603, A_602, C_605]: (r1_tmap_1(k1_tsep_1(A_602, C_605, D_607), B_606, E_604, H_603) | ~r1_tmap_1(D_607, B_606, k3_tmap_1(A_602, B_606, k1_tsep_1(A_602, C_605, D_607), D_607, E_604), H_603) | ~r1_tmap_1(C_605, B_606, k3_tmap_1(A_602, B_606, k1_tsep_1(A_602, C_605, D_607), C_605, E_604), H_603) | ~m1_subset_1(H_603, u1_struct_0(k1_tsep_1(A_602, C_605, D_607))) | ~m1_subset_1(H_603, u1_struct_0(D_607)) | ~m1_subset_1(H_603, u1_struct_0(C_605)) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_602, C_605, D_607)), u1_struct_0(B_606)))) | ~v1_funct_2(E_604, u1_struct_0(k1_tsep_1(A_602, C_605, D_607)), u1_struct_0(B_606)) | ~v1_funct_1(E_604) | ~m1_pre_topc(D_607, A_602) | v2_struct_0(D_607) | ~m1_pre_topc(C_605, A_602) | v2_struct_0(C_605) | ~l1_pre_topc(B_606) | ~v2_pre_topc(B_606) | v2_struct_0(B_606) | ~l1_pre_topc(A_602) | ~v2_pre_topc(A_602) | v2_struct_0(A_602))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.80/1.63  tff(c_367, plain, (![B_606, E_604, H_603]: (r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_606, E_604, H_603) | ~r1_tmap_1('#skF_5', B_606, k3_tmap_1('#skF_1', B_606, '#skF_1', '#skF_5', E_604), H_603) | ~r1_tmap_1('#skF_4', B_606, k3_tmap_1('#skF_1', B_606, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_604), H_603) | ~m1_subset_1(H_603, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_603, u1_struct_0('#skF_5')) | ~m1_subset_1(H_603, u1_struct_0('#skF_4')) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_606)))) | ~v1_funct_2(E_604, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_606)) | ~v1_funct_1(E_604) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_606) | ~v2_pre_topc(B_606) | v2_struct_0(B_606) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_365])).
% 3.80/1.63  tff(c_369, plain, (![B_606, E_604, H_603]: (r1_tmap_1('#skF_1', B_606, E_604, H_603) | ~r1_tmap_1('#skF_5', B_606, k3_tmap_1('#skF_1', B_606, '#skF_1', '#skF_5', E_604), H_603) | ~r1_tmap_1('#skF_4', B_606, k3_tmap_1('#skF_1', B_606, '#skF_1', '#skF_4', E_604), H_603) | ~m1_subset_1(H_603, u1_struct_0('#skF_1')) | ~m1_subset_1(H_603, u1_struct_0('#skF_5')) | ~m1_subset_1(H_603, u1_struct_0('#skF_4')) | ~m1_subset_1(E_604, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_606)))) | ~v1_funct_2(E_604, u1_struct_0('#skF_1'), u1_struct_0(B_606)) | ~v1_funct_1(E_604) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_606) | ~v2_pre_topc(B_606) | v2_struct_0(B_606) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_34, c_30, c_28, c_28, c_28, c_28, c_28, c_367])).
% 3.80/1.63  tff(c_372, plain, (![B_609, E_610, H_611]: (r1_tmap_1('#skF_1', B_609, E_610, H_611) | ~r1_tmap_1('#skF_5', B_609, k3_tmap_1('#skF_1', B_609, '#skF_1', '#skF_5', E_610), H_611) | ~r1_tmap_1('#skF_4', B_609, k3_tmap_1('#skF_1', B_609, '#skF_1', '#skF_4', E_610), H_611) | ~m1_subset_1(H_611, u1_struct_0('#skF_1')) | ~m1_subset_1(H_611, u1_struct_0('#skF_5')) | ~m1_subset_1(H_611, u1_struct_0('#skF_4')) | ~m1_subset_1(E_610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_609)))) | ~v1_funct_2(E_610, u1_struct_0('#skF_1'), u1_struct_0(B_609)) | ~v1_funct_1(E_610) | ~l1_pre_topc(B_609) | ~v2_pre_topc(B_609) | v2_struct_0(B_609))), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_369])).
% 3.80/1.63  tff(c_374, plain, (![H_611]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_611) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_611) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), H_611) | ~m1_subset_1(H_611, u1_struct_0('#skF_1')) | ~m1_subset_1(H_611, u1_struct_0('#skF_5')) | ~m1_subset_1(H_611, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_227, c_372])).
% 3.80/1.63  tff(c_376, plain, (![H_611]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_611) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_611) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_611) | ~m1_subset_1(H_611, u1_struct_0('#skF_1')) | ~m1_subset_1(H_611, u1_struct_0('#skF_5')) | ~m1_subset_1(H_611, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_210, c_374])).
% 3.80/1.63  tff(c_378, plain, (![H_612]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_612) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_612) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_612) | ~m1_subset_1(H_612, u1_struct_0('#skF_1')) | ~m1_subset_1(H_612, u1_struct_0('#skF_5')) | ~m1_subset_1(H_612, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_376])).
% 3.80/1.63  tff(c_384, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_88, c_378])).
% 3.80/1.63  tff(c_388, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_22, c_71, c_89, c_384])).
% 3.80/1.63  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_388])).
% 3.80/1.63  tff(c_391, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 3.80/1.63  tff(c_415, plain, (![A_619, B_620, C_621]: (m1_pre_topc(k1_tsep_1(A_619, B_620, C_621), A_619) | ~m1_pre_topc(C_621, A_619) | v2_struct_0(C_621) | ~m1_pre_topc(B_620, A_619) | v2_struct_0(B_620) | ~l1_pre_topc(A_619) | v2_struct_0(A_619))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.80/1.63  tff(c_418, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_415])).
% 3.80/1.63  tff(c_420, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34, c_30, c_418])).
% 3.80/1.63  tff(c_421, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_420])).
% 3.80/1.63  tff(c_438, plain, (![C_630, B_627, E_628, A_631, D_629]: (k3_tmap_1(A_631, B_627, C_630, D_629, E_628)=k2_partfun1(u1_struct_0(C_630), u1_struct_0(B_627), E_628, u1_struct_0(D_629)) | ~m1_pre_topc(D_629, C_630) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_630), u1_struct_0(B_627)))) | ~v1_funct_2(E_628, u1_struct_0(C_630), u1_struct_0(B_627)) | ~v1_funct_1(E_628) | ~m1_pre_topc(D_629, A_631) | ~m1_pre_topc(C_630, A_631) | ~l1_pre_topc(B_627) | ~v2_pre_topc(B_627) | v2_struct_0(B_627) | ~l1_pre_topc(A_631) | ~v2_pre_topc(A_631) | v2_struct_0(A_631))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.80/1.63  tff(c_440, plain, (![A_631, D_629]: (k3_tmap_1(A_631, '#skF_2', '#skF_1', D_629, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_629)) | ~m1_pre_topc(D_629, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_629, A_631) | ~m1_pre_topc('#skF_1', A_631) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_631) | ~v2_pre_topc(A_631) | v2_struct_0(A_631))), inference(resolution, [status(thm)], [c_38, c_438])).
% 3.80/1.63  tff(c_443, plain, (![A_631, D_629]: (k3_tmap_1(A_631, '#skF_2', '#skF_1', D_629, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_629)) | ~m1_pre_topc(D_629, '#skF_1') | ~m1_pre_topc(D_629, A_631) | ~m1_pre_topc('#skF_1', A_631) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_631) | ~v2_pre_topc(A_631) | v2_struct_0(A_631))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_440])).
% 3.80/1.63  tff(c_445, plain, (![A_632, D_633]: (k3_tmap_1(A_632, '#skF_2', '#skF_1', D_633, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_633)) | ~m1_pre_topc(D_633, '#skF_1') | ~m1_pre_topc(D_633, A_632) | ~m1_pre_topc('#skF_1', A_632) | ~l1_pre_topc(A_632) | ~v2_pre_topc(A_632) | v2_struct_0(A_632))), inference(negUnitSimplification, [status(thm)], [c_48, c_443])).
% 3.80/1.63  tff(c_453, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_445])).
% 3.80/1.63  tff(c_465, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_421, c_34, c_453])).
% 3.80/1.63  tff(c_466, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_465])).
% 3.80/1.63  tff(c_422, plain, (![A_622, B_623, C_624, D_625]: (k2_partfun1(u1_struct_0(A_622), u1_struct_0(B_623), C_624, u1_struct_0(D_625))=k2_tmap_1(A_622, B_623, C_624, D_625) | ~m1_pre_topc(D_625, A_622) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_622), u1_struct_0(B_623)))) | ~v1_funct_2(C_624, u1_struct_0(A_622), u1_struct_0(B_623)) | ~v1_funct_1(C_624) | ~l1_pre_topc(B_623) | ~v2_pre_topc(B_623) | v2_struct_0(B_623) | ~l1_pre_topc(A_622) | ~v2_pre_topc(A_622) | v2_struct_0(A_622))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.80/1.63  tff(c_424, plain, (![D_625]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_625))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_625) | ~m1_pre_topc(D_625, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_422])).
% 3.80/1.63  tff(c_427, plain, (![D_625]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_625))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_625) | ~m1_pre_topc(D_625, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_42, c_40, c_424])).
% 3.80/1.63  tff(c_428, plain, (![D_625]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_625))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_625) | ~m1_pre_topc(D_625, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_427])).
% 3.80/1.63  tff(c_496, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_466, c_428])).
% 3.80/1.63  tff(c_503, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_496])).
% 3.80/1.63  tff(c_467, plain, (![A_634, B_638, E_636, C_637, D_639, H_635]: (r1_tmap_1(C_637, B_638, k3_tmap_1(A_634, B_638, k1_tsep_1(A_634, C_637, D_639), C_637, E_636), H_635) | ~r1_tmap_1(k1_tsep_1(A_634, C_637, D_639), B_638, E_636, H_635) | ~m1_subset_1(H_635, u1_struct_0(k1_tsep_1(A_634, C_637, D_639))) | ~m1_subset_1(H_635, u1_struct_0(D_639)) | ~m1_subset_1(H_635, u1_struct_0(C_637)) | ~m1_subset_1(E_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_634, C_637, D_639)), u1_struct_0(B_638)))) | ~v1_funct_2(E_636, u1_struct_0(k1_tsep_1(A_634, C_637, D_639)), u1_struct_0(B_638)) | ~v1_funct_1(E_636) | ~m1_pre_topc(D_639, A_634) | v2_struct_0(D_639) | ~m1_pre_topc(C_637, A_634) | v2_struct_0(C_637) | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638) | ~l1_pre_topc(A_634) | ~v2_pre_topc(A_634) | v2_struct_0(A_634))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.80/1.63  tff(c_469, plain, (![B_638, E_636, H_635]: (r1_tmap_1('#skF_4', B_638, k3_tmap_1('#skF_1', B_638, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_4', E_636), H_635) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_638, E_636, H_635) | ~m1_subset_1(H_635, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_635, u1_struct_0('#skF_5')) | ~m1_subset_1(H_635, u1_struct_0('#skF_4')) | ~m1_subset_1(E_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_638)))) | ~v1_funct_2(E_636, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_638)) | ~v1_funct_1(E_636) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_467])).
% 3.80/1.63  tff(c_471, plain, (![B_638, E_636, H_635]: (r1_tmap_1('#skF_4', B_638, k3_tmap_1('#skF_1', B_638, '#skF_1', '#skF_4', E_636), H_635) | ~r1_tmap_1('#skF_1', B_638, E_636, H_635) | ~m1_subset_1(H_635, u1_struct_0('#skF_1')) | ~m1_subset_1(H_635, u1_struct_0('#skF_5')) | ~m1_subset_1(H_635, u1_struct_0('#skF_4')) | ~m1_subset_1(E_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_638)))) | ~v1_funct_2(E_636, u1_struct_0('#skF_1'), u1_struct_0(B_638)) | ~v1_funct_1(E_636) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_638) | ~v2_pre_topc(B_638) | v2_struct_0(B_638) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_34, c_30, c_28, c_28, c_28, c_28, c_469])).
% 3.80/1.63  tff(c_673, plain, (![B_666, E_667, H_668]: (r1_tmap_1('#skF_4', B_666, k3_tmap_1('#skF_1', B_666, '#skF_1', '#skF_4', E_667), H_668) | ~r1_tmap_1('#skF_1', B_666, E_667, H_668) | ~m1_subset_1(H_668, u1_struct_0('#skF_1')) | ~m1_subset_1(H_668, u1_struct_0('#skF_5')) | ~m1_subset_1(H_668, u1_struct_0('#skF_4')) | ~m1_subset_1(E_667, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_666)))) | ~v1_funct_2(E_667, u1_struct_0('#skF_1'), u1_struct_0(B_666)) | ~v1_funct_1(E_667) | ~l1_pre_topc(B_666) | ~v2_pre_topc(B_666) | v2_struct_0(B_666))), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_471])).
% 3.80/1.63  tff(c_675, plain, (![H_668]: (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3'), H_668) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_668) | ~m1_subset_1(H_668, u1_struct_0('#skF_1')) | ~m1_subset_1(H_668, u1_struct_0('#skF_5')) | ~m1_subset_1(H_668, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_673])).
% 3.80/1.63  tff(c_678, plain, (![H_668]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_668) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_668) | ~m1_subset_1(H_668, u1_struct_0('#skF_1')) | ~m1_subset_1(H_668, u1_struct_0('#skF_5')) | ~m1_subset_1(H_668, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_503, c_675])).
% 3.80/1.63  tff(c_680, plain, (![H_669]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_669) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_669) | ~m1_subset_1(H_669, u1_struct_0('#skF_1')) | ~m1_subset_1(H_669, u1_struct_0('#skF_5')) | ~m1_subset_1(H_669, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_678])).
% 3.80/1.63  tff(c_392, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_75])).
% 3.80/1.63  tff(c_683, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_680, c_392])).
% 3.80/1.63  tff(c_687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_22, c_71, c_391, c_683])).
% 3.80/1.63  tff(c_688, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.80/1.63  tff(c_714, plain, (![A_679, B_680, C_681, D_682]: (k2_partfun1(u1_struct_0(A_679), u1_struct_0(B_680), C_681, u1_struct_0(D_682))=k2_tmap_1(A_679, B_680, C_681, D_682) | ~m1_pre_topc(D_682, A_679) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_679), u1_struct_0(B_680)))) | ~v1_funct_2(C_681, u1_struct_0(A_679), u1_struct_0(B_680)) | ~v1_funct_1(C_681) | ~l1_pre_topc(B_680) | ~v2_pre_topc(B_680) | v2_struct_0(B_680) | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679) | v2_struct_0(A_679))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.80/1.63  tff(c_716, plain, (![D_682]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_682))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_682) | ~m1_pre_topc(D_682, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_714])).
% 3.80/1.63  tff(c_719, plain, (![D_682]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_682))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_682) | ~m1_pre_topc(D_682, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_42, c_40, c_716])).
% 3.80/1.63  tff(c_720, plain, (![D_682]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_682))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_682) | ~m1_pre_topc(D_682, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_719])).
% 3.80/1.63  tff(c_705, plain, (![A_676, B_677, C_678]: (m1_pre_topc(k1_tsep_1(A_676, B_677, C_678), A_676) | ~m1_pre_topc(C_678, A_676) | v2_struct_0(C_678) | ~m1_pre_topc(B_677, A_676) | v2_struct_0(B_677) | ~l1_pre_topc(A_676) | v2_struct_0(A_676))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.80/1.63  tff(c_708, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_705])).
% 3.80/1.63  tff(c_710, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_34, c_30, c_708])).
% 3.80/1.63  tff(c_711, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_710])).
% 3.80/1.63  tff(c_730, plain, (![B_684, E_685, D_686, A_688, C_687]: (k3_tmap_1(A_688, B_684, C_687, D_686, E_685)=k2_partfun1(u1_struct_0(C_687), u1_struct_0(B_684), E_685, u1_struct_0(D_686)) | ~m1_pre_topc(D_686, C_687) | ~m1_subset_1(E_685, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_687), u1_struct_0(B_684)))) | ~v1_funct_2(E_685, u1_struct_0(C_687), u1_struct_0(B_684)) | ~v1_funct_1(E_685) | ~m1_pre_topc(D_686, A_688) | ~m1_pre_topc(C_687, A_688) | ~l1_pre_topc(B_684) | ~v2_pre_topc(B_684) | v2_struct_0(B_684) | ~l1_pre_topc(A_688) | ~v2_pre_topc(A_688) | v2_struct_0(A_688))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.80/1.63  tff(c_732, plain, (![A_688, D_686]: (k3_tmap_1(A_688, '#skF_2', '#skF_1', D_686, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_686)) | ~m1_pre_topc(D_686, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_686, A_688) | ~m1_pre_topc('#skF_1', A_688) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_688) | ~v2_pre_topc(A_688) | v2_struct_0(A_688))), inference(resolution, [status(thm)], [c_38, c_730])).
% 3.80/1.63  tff(c_735, plain, (![A_688, D_686]: (k3_tmap_1(A_688, '#skF_2', '#skF_1', D_686, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_686)) | ~m1_pre_topc(D_686, '#skF_1') | ~m1_pre_topc(D_686, A_688) | ~m1_pre_topc('#skF_1', A_688) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_688) | ~v2_pre_topc(A_688) | v2_struct_0(A_688))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_732])).
% 3.80/1.63  tff(c_737, plain, (![A_689, D_690]: (k3_tmap_1(A_689, '#skF_2', '#skF_1', D_690, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_690)) | ~m1_pre_topc(D_690, '#skF_1') | ~m1_pre_topc(D_690, A_689) | ~m1_pre_topc('#skF_1', A_689) | ~l1_pre_topc(A_689) | ~v2_pre_topc(A_689) | v2_struct_0(A_689))), inference(negUnitSimplification, [status(thm)], [c_48, c_735])).
% 3.80/1.63  tff(c_743, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_737])).
% 3.80/1.63  tff(c_753, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_711, c_30, c_743])).
% 3.80/1.63  tff(c_754, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_753])).
% 3.80/1.63  tff(c_827, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_720, c_754])).
% 3.80/1.63  tff(c_833, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_827])).
% 3.80/1.63  tff(c_873, plain, (![E_699, A_697, H_698, B_701, C_700, D_702]: (r1_tmap_1(D_702, B_701, k3_tmap_1(A_697, B_701, k1_tsep_1(A_697, C_700, D_702), D_702, E_699), H_698) | ~r1_tmap_1(k1_tsep_1(A_697, C_700, D_702), B_701, E_699, H_698) | ~m1_subset_1(H_698, u1_struct_0(k1_tsep_1(A_697, C_700, D_702))) | ~m1_subset_1(H_698, u1_struct_0(D_702)) | ~m1_subset_1(H_698, u1_struct_0(C_700)) | ~m1_subset_1(E_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_697, C_700, D_702)), u1_struct_0(B_701)))) | ~v1_funct_2(E_699, u1_struct_0(k1_tsep_1(A_697, C_700, D_702)), u1_struct_0(B_701)) | ~v1_funct_1(E_699) | ~m1_pre_topc(D_702, A_697) | v2_struct_0(D_702) | ~m1_pre_topc(C_700, A_697) | v2_struct_0(C_700) | ~l1_pre_topc(B_701) | ~v2_pre_topc(B_701) | v2_struct_0(B_701) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.80/1.63  tff(c_875, plain, (![B_701, E_699, H_698]: (r1_tmap_1('#skF_5', B_701, k3_tmap_1('#skF_1', B_701, k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), '#skF_5', E_699), H_698) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_701, E_699, H_698) | ~m1_subset_1(H_698, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1(H_698, u1_struct_0('#skF_5')) | ~m1_subset_1(H_698, u1_struct_0('#skF_4')) | ~m1_subset_1(E_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_701)))) | ~v1_funct_2(E_699, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), u1_struct_0(B_701)) | ~v1_funct_1(E_699) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_701) | ~v2_pre_topc(B_701) | v2_struct_0(B_701) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_873])).
% 3.80/1.63  tff(c_877, plain, (![B_701, E_699, H_698]: (r1_tmap_1('#skF_5', B_701, k3_tmap_1('#skF_1', B_701, '#skF_1', '#skF_5', E_699), H_698) | ~r1_tmap_1('#skF_1', B_701, E_699, H_698) | ~m1_subset_1(H_698, u1_struct_0('#skF_1')) | ~m1_subset_1(H_698, u1_struct_0('#skF_5')) | ~m1_subset_1(H_698, u1_struct_0('#skF_4')) | ~m1_subset_1(E_699, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_701)))) | ~v1_funct_2(E_699, u1_struct_0('#skF_1'), u1_struct_0(B_701)) | ~v1_funct_1(E_699) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~l1_pre_topc(B_701) | ~v2_pre_topc(B_701) | v2_struct_0(B_701) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_34, c_30, c_28, c_28, c_28, c_28, c_875])).
% 3.80/1.63  tff(c_959, plain, (![B_717, E_718, H_719]: (r1_tmap_1('#skF_5', B_717, k3_tmap_1('#skF_1', B_717, '#skF_1', '#skF_5', E_718), H_719) | ~r1_tmap_1('#skF_1', B_717, E_718, H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(E_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_717)))) | ~v1_funct_2(E_718, u1_struct_0('#skF_1'), u1_struct_0(B_717)) | ~v1_funct_1(E_718) | ~l1_pre_topc(B_717) | ~v2_pre_topc(B_717) | v2_struct_0(B_717))), inference(negUnitSimplification, [status(thm)], [c_54, c_36, c_32, c_877])).
% 3.80/1.63  tff(c_961, plain, (![H_719]: (r1_tmap_1('#skF_5', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_5', '#skF_3'), H_719) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_959])).
% 3.80/1.63  tff(c_964, plain, (![H_719]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_719) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_833, c_961])).
% 3.80/1.63  tff(c_966, plain, (![H_720]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_720) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_720) | ~m1_subset_1(H_720, u1_struct_0('#skF_1')) | ~m1_subset_1(H_720, u1_struct_0('#skF_5')) | ~m1_subset_1(H_720, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_964])).
% 3.80/1.63  tff(c_689, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.80/1.63  tff(c_969, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_966, c_689])).
% 3.80/1.63  tff(c_973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_22, c_71, c_688, c_969])).
% 3.80/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  Inference rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Ref     : 0
% 3.80/1.63  #Sup     : 190
% 3.80/1.63  #Fact    : 0
% 3.80/1.63  #Define  : 0
% 3.80/1.63  #Split   : 3
% 3.80/1.63  #Chain   : 0
% 3.80/1.63  #Close   : 0
% 3.80/1.63  
% 3.80/1.63  Ordering : KBO
% 3.80/1.63  
% 3.80/1.63  Simplification rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Subsume      : 11
% 3.80/1.63  #Demod        : 381
% 3.80/1.63  #Tautology    : 129
% 3.80/1.63  #SimpNegUnit  : 58
% 3.80/1.63  #BackRed      : 9
% 3.80/1.63  
% 3.80/1.63  #Partial instantiations: 0
% 3.80/1.63  #Strategies tried      : 1
% 3.80/1.63  
% 3.80/1.63  Timing (in seconds)
% 3.80/1.63  ----------------------
% 3.80/1.63  Preprocessing        : 0.40
% 3.80/1.63  Parsing              : 0.20
% 3.80/1.64  CNF conversion       : 0.07
% 3.80/1.64  Main loop            : 0.44
% 3.80/1.64  Inferencing          : 0.16
% 3.80/1.64  Reduction            : 0.15
% 3.80/1.64  Demodulation         : 0.11
% 3.80/1.64  BG Simplification    : 0.03
% 3.80/1.64  Subsumption          : 0.07
% 3.80/1.64  Abstraction          : 0.02
% 3.80/1.64  MUC search           : 0.00
% 3.80/1.64  Cooper               : 0.00
% 3.80/1.64  Total                : 0.90
% 3.80/1.64  Index Insertion      : 0.00
% 3.80/1.64  Index Deletion       : 0.00
% 3.80/1.64  Index Matching       : 0.00
% 3.80/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
