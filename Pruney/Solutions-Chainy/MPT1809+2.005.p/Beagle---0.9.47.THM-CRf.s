%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:05 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :  281 (8575 expanded)
%              Number of leaves         :   37 (3323 expanded)
%              Depth                    :   24
%              Number of atoms          : 1142 (86166 expanded)
%              Number of equality atoms :   87 (11050 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_265,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_179,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_104,axiom,(
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

tff(f_72,axiom,(
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

tff(f_209,axiom,(
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
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_175,axiom,(
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

tff(c_28,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_81,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_30,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_78,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_79,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_76])).

tff(c_85,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_79])).

tff(c_101,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_100,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_77,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_77])).

tff(c_109,plain,(
    ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_100,c_83])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_38,plain,(
    k1_tsep_1('#skF_1','#skF_4','#skF_5') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_110,plain,(
    ! [A_579,B_580,C_581,D_582] :
      ( v1_funct_1(k2_tmap_1(A_579,B_580,C_581,D_582))
      | ~ l1_struct_0(D_582)
      | ~ m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_579),u1_struct_0(B_580))))
      | ~ v1_funct_2(C_581,u1_struct_0(A_579),u1_struct_0(B_580))
      | ~ v1_funct_1(C_581)
      | ~ l1_struct_0(B_580)
      | ~ l1_struct_0(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_112,plain,(
    ! [D_582] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_582))
      | ~ l1_struct_0(D_582)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_110])).

tff(c_115,plain,(
    ! [D_582] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_582))
      | ~ l1_struct_0(D_582)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_112])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_119])).

tff(c_125,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_124,plain,(
    ! [D_582] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_582))
      | ~ l1_struct_0(D_582) ) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_126,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_129,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_135,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_144,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( v1_funct_2(k2_tmap_1(A_588,B_589,C_590,D_591),u1_struct_0(D_591),u1_struct_0(B_589))
      | ~ l1_struct_0(D_591)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_588),u1_struct_0(B_589))))
      | ~ v1_funct_2(C_590,u1_struct_0(A_588),u1_struct_0(B_589))
      | ~ v1_funct_1(C_590)
      | ~ l1_struct_0(B_589)
      | ~ l1_struct_0(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_146,plain,(
    ! [D_591] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_591),u1_struct_0(D_591),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_591)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_144])).

tff(c_149,plain,(
    ! [D_591] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_591),u1_struct_0(D_591),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_135,c_52,c_50,c_146])).

tff(c_12,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( m1_subset_1(k2_tmap_1(A_52,B_53,C_54,D_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_55),u1_struct_0(B_53))))
      | ~ l1_struct_0(D_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52),u1_struct_0(B_53))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_52),u1_struct_0(B_53))
      | ~ v1_funct_1(C_54)
      | ~ l1_struct_0(B_53)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_134,plain,(
    ! [D_582] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_582))
      | ~ l1_struct_0(D_582) ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_24,plain,(
    ! [A_311] :
      ( m1_pre_topc(A_311,A_311)
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_197,plain,(
    ! [C_611,B_612,D_610,E_608,A_609] :
      ( k3_tmap_1(A_609,B_612,C_611,D_610,E_608) = k2_partfun1(u1_struct_0(C_611),u1_struct_0(B_612),E_608,u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,C_611)
      | ~ m1_subset_1(E_608,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_611),u1_struct_0(B_612))))
      | ~ v1_funct_2(E_608,u1_struct_0(C_611),u1_struct_0(B_612))
      | ~ v1_funct_1(E_608)
      | ~ m1_pre_topc(D_610,A_609)
      | ~ m1_pre_topc(C_611,A_609)
      | ~ l1_pre_topc(B_612)
      | ~ v2_pre_topc(B_612)
      | v2_struct_0(B_612)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_201,plain,(
    ! [A_609,D_610] :
      ( k3_tmap_1(A_609,'#skF_2','#skF_1',D_610,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_610,A_609)
      | ~ m1_pre_topc('#skF_1',A_609)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(resolution,[status(thm)],[c_48,c_197])).

tff(c_205,plain,(
    ! [A_609,D_610] :
      ( k3_tmap_1(A_609,'#skF_2','#skF_1',D_610,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_1')
      | ~ m1_pre_topc(D_610,A_609)
      | ~ m1_pre_topc('#skF_1',A_609)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_201])).

tff(c_207,plain,(
    ! [A_613,D_614] :
      ( k3_tmap_1(A_613,'#skF_2','#skF_1',D_614,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_614))
      | ~ m1_pre_topc(D_614,'#skF_1')
      | ~ m1_pre_topc(D_614,A_613)
      | ~ m1_pre_topc('#skF_1',A_613)
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_205])).

tff(c_211,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_207])).

tff(c_217,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_211])).

tff(c_218,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_217])).

tff(c_223,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_226,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_226])).

tff(c_232,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_206,plain,(
    ! [A_609,D_610] :
      ( k3_tmap_1(A_609,'#skF_2','#skF_1',D_610,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_1')
      | ~ m1_pre_topc(D_610,A_609)
      | ~ m1_pre_topc('#skF_1',A_609)
      | ~ l1_pre_topc(A_609)
      | ~ v2_pre_topc(A_609)
      | v2_struct_0(A_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_205])).

tff(c_245,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_232,c_206])).

tff(c_248,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_232,c_245])).

tff(c_249,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_248])).

tff(c_161,plain,(
    ! [A_597,B_598,C_599,D_600] :
      ( k2_partfun1(u1_struct_0(A_597),u1_struct_0(B_598),C_599,u1_struct_0(D_600)) = k2_tmap_1(A_597,B_598,C_599,D_600)
      | ~ m1_pre_topc(D_600,A_597)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_597),u1_struct_0(B_598))))
      | ~ v1_funct_2(C_599,u1_struct_0(A_597),u1_struct_0(B_598))
      | ~ v1_funct_1(C_599)
      | ~ l1_pre_topc(B_598)
      | ~ v2_pre_topc(B_598)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,(
    ! [D_600] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_600)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_600)
      | ~ m1_pre_topc(D_600,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_161])).

tff(c_169,plain,(
    ! [D_600] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_600)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_600)
      | ~ m1_pre_topc(D_600,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_165])).

tff(c_170,plain,(
    ! [D_600] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_600)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_600)
      | ~ m1_pre_topc(D_600,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_169])).

tff(c_301,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_170])).

tff(c_308,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_301])).

tff(c_180,plain,(
    ! [C_602,B_603,D_604,A_605] :
      ( r2_funct_2(u1_struct_0(C_602),u1_struct_0(B_603),D_604,k3_tmap_1(A_605,B_603,C_602,C_602,D_604))
      | ~ m1_subset_1(D_604,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_602),u1_struct_0(B_603))))
      | ~ v1_funct_2(D_604,u1_struct_0(C_602),u1_struct_0(B_603))
      | ~ v1_funct_1(D_604)
      | ~ m1_pre_topc(C_602,A_605)
      | v2_struct_0(C_602)
      | ~ l1_pre_topc(B_603)
      | ~ v2_pre_topc(B_603)
      | v2_struct_0(B_603)
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_184,plain,(
    ! [A_605] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_605,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_605)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_188,plain,(
    ! [A_605] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_605,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_605)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_605)
      | ~ v2_pre_topc(A_605)
      | v2_struct_0(A_605) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_184])).

tff(c_190,plain,(
    ! [A_606] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_188])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [A_606] :
      ( k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_195,plain,(
    ! [A_606] :
      ( k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_606,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_192])).

tff(c_316,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_195])).

tff(c_323,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_232,c_308,c_308,c_308,c_316])).

tff(c_324,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_323])).

tff(c_398,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_401,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_398])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_401])).

tff(c_406,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_505,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_508,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_505])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_135,c_52,c_50,c_48,c_508])).

tff(c_513,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_560,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_563,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_149,c_560])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_563])).

tff(c_568,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_468,plain,(
    ! [B_631,A_633,H_632,D_628,E_630,C_629] :
      ( r1_tmap_1(k1_tsep_1(A_633,D_628,E_630),B_631,k2_tmap_1(A_633,B_631,C_629,k1_tsep_1(A_633,D_628,E_630)),H_632)
      | ~ r1_tmap_1(E_630,B_631,k2_tmap_1(A_633,B_631,C_629,E_630),H_632)
      | ~ r1_tmap_1(D_628,B_631,k2_tmap_1(A_633,B_631,C_629,D_628),H_632)
      | ~ m1_subset_1(H_632,u1_struct_0(E_630))
      | ~ m1_subset_1(H_632,u1_struct_0(D_628))
      | ~ m1_subset_1(H_632,u1_struct_0(k1_tsep_1(A_633,D_628,E_630)))
      | ~ m1_pre_topc(E_630,A_633)
      | v2_struct_0(E_630)
      | ~ m1_pre_topc(D_628,A_633)
      | v2_struct_0(D_628)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_633),u1_struct_0(B_631))))
      | ~ v1_funct_2(C_629,u1_struct_0(A_633),u1_struct_0(B_631))
      | ~ v1_funct_1(C_629)
      | ~ l1_pre_topc(B_631)
      | ~ v2_pre_topc(B_631)
      | v2_struct_0(B_631)
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_472,plain,(
    ! [D_628,E_630,H_632] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_628,E_630),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_628,E_630)),H_632)
      | ~ r1_tmap_1(E_630,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_630),H_632)
      | ~ r1_tmap_1(D_628,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628),H_632)
      | ~ m1_subset_1(H_632,u1_struct_0(E_630))
      | ~ m1_subset_1(H_632,u1_struct_0(D_628))
      | ~ m1_subset_1(H_632,u1_struct_0(k1_tsep_1('#skF_1',D_628,E_630)))
      | ~ m1_pre_topc(E_630,'#skF_1')
      | v2_struct_0(E_630)
      | ~ m1_pre_topc(D_628,'#skF_1')
      | v2_struct_0(D_628)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_468])).

tff(c_476,plain,(
    ! [D_628,E_630,H_632] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_628,E_630),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_628,E_630)),H_632)
      | ~ r1_tmap_1(E_630,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_630),H_632)
      | ~ r1_tmap_1(D_628,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_628),H_632)
      | ~ m1_subset_1(H_632,u1_struct_0(E_630))
      | ~ m1_subset_1(H_632,u1_struct_0(D_628))
      | ~ m1_subset_1(H_632,u1_struct_0(k1_tsep_1('#skF_1',D_628,E_630)))
      | ~ m1_pre_topc(E_630,'#skF_1')
      | v2_struct_0(E_630)
      | ~ m1_pre_topc(D_628,'#skF_1')
      | v2_struct_0(D_628)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_472])).

tff(c_709,plain,(
    ! [D_659,E_660,H_661] :
      ( r1_tmap_1(k1_tsep_1('#skF_1',D_659,E_660),'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',D_659,E_660)),H_661)
      | ~ r1_tmap_1(E_660,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',E_660),H_661)
      | ~ r1_tmap_1(D_659,'#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',D_659),H_661)
      | ~ m1_subset_1(H_661,u1_struct_0(E_660))
      | ~ m1_subset_1(H_661,u1_struct_0(D_659))
      | ~ m1_subset_1(H_661,u1_struct_0(k1_tsep_1('#skF_1',D_659,E_660)))
      | ~ m1_pre_topc(E_660,'#skF_1')
      | v2_struct_0(E_660)
      | ~ m1_pre_topc(D_659,'#skF_1')
      | v2_struct_0(D_659) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_476])).

tff(c_716,plain,(
    ! [H_661] :
      ( r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_661)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_661)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_661)
      | ~ m1_subset_1(H_661,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_661,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_661,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_709])).

tff(c_729,plain,(
    ! [H_661] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_661)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_661)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_661)
      | ~ m1_subset_1(H_661,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_661,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_661,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_568,c_38,c_716])).

tff(c_734,plain,(
    ! [H_662] :
      ( r1_tmap_1('#skF_1','#skF_2','#skF_3',H_662)
      | ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_662)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_662)
      | ~ m1_subset_1(H_662,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_662,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_662,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_729])).

tff(c_740,plain,
    ( r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_100,c_734])).

tff(c_744,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_84,c_32,c_101,c_740])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_744])).

tff(c_747,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_757,plain,(
    ! [A_666,B_667,C_668,D_669] :
      ( v1_funct_1(k2_tmap_1(A_666,B_667,C_668,D_669))
      | ~ l1_struct_0(D_669)
      | ~ m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_666),u1_struct_0(B_667))))
      | ~ v1_funct_2(C_668,u1_struct_0(A_666),u1_struct_0(B_667))
      | ~ v1_funct_1(C_668)
      | ~ l1_struct_0(B_667)
      | ~ l1_struct_0(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_759,plain,(
    ! [D_669] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_669))
      | ~ l1_struct_0(D_669)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_757])).

tff(c_762,plain,(
    ! [D_669] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_669))
      | ~ l1_struct_0(D_669)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_759])).

tff(c_763,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_762])).

tff(c_766,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_763])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_766])).

tff(c_772,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_771,plain,(
    ! [D_669] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_669))
      | ~ l1_struct_0(D_669) ) ),
    inference(splitRight,[status(thm)],[c_762])).

tff(c_773,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_776,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_773])).

tff(c_780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_776])).

tff(c_782,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_791,plain,(
    ! [A_675,B_676,C_677,D_678] :
      ( v1_funct_2(k2_tmap_1(A_675,B_676,C_677,D_678),u1_struct_0(D_678),u1_struct_0(B_676))
      | ~ l1_struct_0(D_678)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_675),u1_struct_0(B_676))))
      | ~ v1_funct_2(C_677,u1_struct_0(A_675),u1_struct_0(B_676))
      | ~ v1_funct_1(C_677)
      | ~ l1_struct_0(B_676)
      | ~ l1_struct_0(A_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_793,plain,(
    ! [D_678] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_678),u1_struct_0(D_678),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_678)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_791])).

tff(c_796,plain,(
    ! [D_678] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_678),u1_struct_0(D_678),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_782,c_52,c_50,c_793])).

tff(c_781,plain,(
    ! [D_669] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_669))
      | ~ l1_struct_0(D_669) ) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_851,plain,(
    ! [C_705,E_702,D_704,A_703,B_706] :
      ( k3_tmap_1(A_703,B_706,C_705,D_704,E_702) = k2_partfun1(u1_struct_0(C_705),u1_struct_0(B_706),E_702,u1_struct_0(D_704))
      | ~ m1_pre_topc(D_704,C_705)
      | ~ m1_subset_1(E_702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_705),u1_struct_0(B_706))))
      | ~ v1_funct_2(E_702,u1_struct_0(C_705),u1_struct_0(B_706))
      | ~ v1_funct_1(E_702)
      | ~ m1_pre_topc(D_704,A_703)
      | ~ m1_pre_topc(C_705,A_703)
      | ~ l1_pre_topc(B_706)
      | ~ v2_pre_topc(B_706)
      | v2_struct_0(B_706)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_855,plain,(
    ! [A_703,D_704] :
      ( k3_tmap_1(A_703,'#skF_2','#skF_1',D_704,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_704))
      | ~ m1_pre_topc(D_704,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_704,A_703)
      | ~ m1_pre_topc('#skF_1',A_703)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(resolution,[status(thm)],[c_48,c_851])).

tff(c_859,plain,(
    ! [A_703,D_704] :
      ( k3_tmap_1(A_703,'#skF_2','#skF_1',D_704,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_704))
      | ~ m1_pre_topc(D_704,'#skF_1')
      | ~ m1_pre_topc(D_704,A_703)
      | ~ m1_pre_topc('#skF_1',A_703)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_855])).

tff(c_872,plain,(
    ! [A_713,D_714] :
      ( k3_tmap_1(A_713,'#skF_2','#skF_1',D_714,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_714))
      | ~ m1_pre_topc(D_714,'#skF_1')
      | ~ m1_pre_topc(D_714,A_713)
      | ~ m1_pre_topc('#skF_1',A_713)
      | ~ l1_pre_topc(A_713)
      | ~ v2_pre_topc(A_713)
      | v2_struct_0(A_713) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_859])).

tff(c_876,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_872])).

tff(c_882,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_876])).

tff(c_883,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_882])).

tff(c_888,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_891,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_888])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_891])).

tff(c_897,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_860,plain,(
    ! [A_703,D_704] :
      ( k3_tmap_1(A_703,'#skF_2','#skF_1',D_704,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_704))
      | ~ m1_pre_topc(D_704,'#skF_1')
      | ~ m1_pre_topc(D_704,A_703)
      | ~ m1_pre_topc('#skF_1',A_703)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_859])).

tff(c_910,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_897,c_860])).

tff(c_913,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_897,c_910])).

tff(c_914,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_913])).

tff(c_808,plain,(
    ! [A_684,B_685,C_686,D_687] :
      ( k2_partfun1(u1_struct_0(A_684),u1_struct_0(B_685),C_686,u1_struct_0(D_687)) = k2_tmap_1(A_684,B_685,C_686,D_687)
      | ~ m1_pre_topc(D_687,A_684)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_684),u1_struct_0(B_685))))
      | ~ v1_funct_2(C_686,u1_struct_0(A_684),u1_struct_0(B_685))
      | ~ v1_funct_1(C_686)
      | ~ l1_pre_topc(B_685)
      | ~ v2_pre_topc(B_685)
      | v2_struct_0(B_685)
      | ~ l1_pre_topc(A_684)
      | ~ v2_pre_topc(A_684)
      | v2_struct_0(A_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_812,plain,(
    ! [D_687] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_687)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_687)
      | ~ m1_pre_topc(D_687,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_808])).

tff(c_816,plain,(
    ! [D_687] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_687)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_687)
      | ~ m1_pre_topc(D_687,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_812])).

tff(c_817,plain,(
    ! [D_687] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_687)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_687)
      | ~ m1_pre_topc(D_687,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_816])).

tff(c_966,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_817])).

tff(c_973,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_966])).

tff(c_827,plain,(
    ! [C_689,B_690,D_691,A_692] :
      ( r2_funct_2(u1_struct_0(C_689),u1_struct_0(B_690),D_691,k3_tmap_1(A_692,B_690,C_689,C_689,D_691))
      | ~ m1_subset_1(D_691,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_689),u1_struct_0(B_690))))
      | ~ v1_funct_2(D_691,u1_struct_0(C_689),u1_struct_0(B_690))
      | ~ v1_funct_1(D_691)
      | ~ m1_pre_topc(C_689,A_692)
      | v2_struct_0(C_689)
      | ~ l1_pre_topc(B_690)
      | ~ v2_pre_topc(B_690)
      | v2_struct_0(B_690)
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_831,plain,(
    ! [A_692] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_692,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_692)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(resolution,[status(thm)],[c_48,c_827])).

tff(c_835,plain,(
    ! [A_692] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_692,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_692)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_692)
      | ~ v2_pre_topc(A_692)
      | v2_struct_0(A_692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_831])).

tff(c_837,plain,(
    ! [A_693] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_693)
      | ~ l1_pre_topc(A_693)
      | ~ v2_pre_topc(A_693)
      | v2_struct_0(A_693) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_835])).

tff(c_839,plain,(
    ! [A_693] :
      ( k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_693)
      | ~ l1_pre_topc(A_693)
      | ~ v2_pre_topc(A_693)
      | v2_struct_0(A_693) ) ),
    inference(resolution,[status(thm)],[c_837,c_4])).

tff(c_842,plain,(
    ! [A_693] :
      ( k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_693,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_693)
      | ~ l1_pre_topc(A_693)
      | ~ v2_pre_topc(A_693)
      | v2_struct_0(A_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_839])).

tff(c_981,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_842])).

tff(c_988,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_897,c_973,c_973,c_973,c_981])).

tff(c_989,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_988])).

tff(c_1062,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_989])).

tff(c_1065,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_781,c_1062])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1065])).

tff(c_1070,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_1172,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1070])).

tff(c_1175,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1172])).

tff(c_1179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_782,c_52,c_50,c_48,c_1175])).

tff(c_1180,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1070])).

tff(c_1228,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1180])).

tff(c_1231,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_796,c_1228])).

tff(c_1235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1231])).

tff(c_1236,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1180])).

tff(c_930,plain,(
    ! [E_717,C_716,H_719,D_715,B_718,A_720] :
      ( r1_tmap_1(D_715,B_718,k2_tmap_1(A_720,B_718,C_716,D_715),H_719)
      | ~ r1_tmap_1(k1_tsep_1(A_720,D_715,E_717),B_718,k2_tmap_1(A_720,B_718,C_716,k1_tsep_1(A_720,D_715,E_717)),H_719)
      | ~ m1_subset_1(H_719,u1_struct_0(E_717))
      | ~ m1_subset_1(H_719,u1_struct_0(D_715))
      | ~ m1_subset_1(H_719,u1_struct_0(k1_tsep_1(A_720,D_715,E_717)))
      | ~ m1_pre_topc(E_717,A_720)
      | v2_struct_0(E_717)
      | ~ m1_pre_topc(D_715,A_720)
      | v2_struct_0(D_715)
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_720),u1_struct_0(B_718))))
      | ~ v1_funct_2(C_716,u1_struct_0(A_720),u1_struct_0(B_718))
      | ~ v1_funct_1(C_716)
      | ~ l1_pre_topc(B_718)
      | ~ v2_pre_topc(B_718)
      | v2_struct_0(B_718)
      | ~ l1_pre_topc(A_720)
      | ~ v2_pre_topc(A_720)
      | v2_struct_0(A_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_934,plain,(
    ! [B_718,C_716,H_719] :
      ( r1_tmap_1('#skF_4',B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_4'),H_719)
      | ~ r1_tmap_1(k1_tsep_1('#skF_1','#skF_4','#skF_5'),B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_1'),H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_719,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_718))))
      | ~ v1_funct_2(C_716,u1_struct_0('#skF_1'),u1_struct_0(B_718))
      | ~ v1_funct_1(C_716)
      | ~ l1_pre_topc(B_718)
      | ~ v2_pre_topc(B_718)
      | v2_struct_0(B_718)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_930])).

tff(c_939,plain,(
    ! [B_718,C_716,H_719] :
      ( r1_tmap_1('#skF_4',B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_4'),H_719)
      | ~ r1_tmap_1('#skF_1',B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_1'),H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_718))))
      | ~ v1_funct_2(C_716,u1_struct_0('#skF_1'),u1_struct_0(B_718))
      | ~ v1_funct_1(C_716)
      | ~ l1_pre_topc(B_718)
      | ~ v2_pre_topc(B_718)
      | v2_struct_0(B_718)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_38,c_38,c_934])).

tff(c_940,plain,(
    ! [B_718,C_716,H_719] :
      ( r1_tmap_1('#skF_4',B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_4'),H_719)
      | ~ r1_tmap_1('#skF_1',B_718,k2_tmap_1('#skF_1',B_718,C_716,'#skF_1'),H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_718))))
      | ~ v1_funct_2(C_716,u1_struct_0('#skF_1'),u1_struct_0(B_718))
      | ~ v1_funct_1(C_716)
      | ~ l1_pre_topc(B_718)
      | ~ v2_pre_topc(B_718)
      | v2_struct_0(B_718) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_939])).

tff(c_1248,plain,(
    ! [H_719] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_719)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_940])).

tff(c_1266,plain,(
    ! [H_719] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_719)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_719)
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_719,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_1248])).

tff(c_1279,plain,(
    ! [H_735] :
      ( r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),H_735)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_735)
      | ~ m1_subset_1(H_735,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_735,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_735,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1266])).

tff(c_748,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_1282,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1279,c_748])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_84,c_32,c_747,c_1282])).

tff(c_1287,plain,(
    r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1298,plain,(
    ! [A_739,B_740,C_741,D_742] :
      ( v1_funct_1(k2_tmap_1(A_739,B_740,C_741,D_742))
      | ~ l1_struct_0(D_742)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_739),u1_struct_0(B_740))))
      | ~ v1_funct_2(C_741,u1_struct_0(A_739),u1_struct_0(B_740))
      | ~ v1_funct_1(C_741)
      | ~ l1_struct_0(B_740)
      | ~ l1_struct_0(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1300,plain,(
    ! [D_742] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_742))
      | ~ l1_struct_0(D_742)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1298])).

tff(c_1303,plain,(
    ! [D_742] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_742))
      | ~ l1_struct_0(D_742)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1300])).

tff(c_1304,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1303])).

tff(c_1307,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_1304])).

tff(c_1311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1307])).

tff(c_1313,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1303])).

tff(c_1312,plain,(
    ! [D_742] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_742))
      | ~ l1_struct_0(D_742) ) ),
    inference(splitRight,[status(thm)],[c_1303])).

tff(c_1314,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1312])).

tff(c_1317,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_1314])).

tff(c_1321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1317])).

tff(c_1323,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1312])).

tff(c_1332,plain,(
    ! [A_748,B_749,C_750,D_751] :
      ( v1_funct_2(k2_tmap_1(A_748,B_749,C_750,D_751),u1_struct_0(D_751),u1_struct_0(B_749))
      | ~ l1_struct_0(D_751)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_748),u1_struct_0(B_749))))
      | ~ v1_funct_2(C_750,u1_struct_0(A_748),u1_struct_0(B_749))
      | ~ v1_funct_1(C_750)
      | ~ l1_struct_0(B_749)
      | ~ l1_struct_0(A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1334,plain,(
    ! [D_751] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_751),u1_struct_0(D_751),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_751)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1332])).

tff(c_1337,plain,(
    ! [D_751] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_751),u1_struct_0(D_751),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1323,c_52,c_50,c_1334])).

tff(c_1322,plain,(
    ! [D_742] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',D_742))
      | ~ l1_struct_0(D_742) ) ),
    inference(splitRight,[status(thm)],[c_1312])).

tff(c_1392,plain,(
    ! [C_778,B_779,E_775,D_777,A_776] :
      ( k3_tmap_1(A_776,B_779,C_778,D_777,E_775) = k2_partfun1(u1_struct_0(C_778),u1_struct_0(B_779),E_775,u1_struct_0(D_777))
      | ~ m1_pre_topc(D_777,C_778)
      | ~ m1_subset_1(E_775,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_778),u1_struct_0(B_779))))
      | ~ v1_funct_2(E_775,u1_struct_0(C_778),u1_struct_0(B_779))
      | ~ v1_funct_1(E_775)
      | ~ m1_pre_topc(D_777,A_776)
      | ~ m1_pre_topc(C_778,A_776)
      | ~ l1_pre_topc(B_779)
      | ~ v2_pre_topc(B_779)
      | v2_struct_0(B_779)
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1396,plain,(
    ! [A_776,D_777] :
      ( k3_tmap_1(A_776,'#skF_2','#skF_1',D_777,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_777))
      | ~ m1_pre_topc(D_777,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc(D_777,A_776)
      | ~ m1_pre_topc('#skF_1',A_776)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(resolution,[status(thm)],[c_48,c_1392])).

tff(c_1400,plain,(
    ! [A_776,D_777] :
      ( k3_tmap_1(A_776,'#skF_2','#skF_1',D_777,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_777))
      | ~ m1_pre_topc(D_777,'#skF_1')
      | ~ m1_pre_topc(D_777,A_776)
      | ~ m1_pre_topc('#skF_1',A_776)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1396])).

tff(c_1402,plain,(
    ! [A_780,D_781] :
      ( k3_tmap_1(A_780,'#skF_2','#skF_1',D_781,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_781))
      | ~ m1_pre_topc(D_781,'#skF_1')
      | ~ m1_pre_topc(D_781,A_780)
      | ~ m1_pre_topc('#skF_1',A_780)
      | ~ l1_pre_topc(A_780)
      | ~ v2_pre_topc(A_780)
      | v2_struct_0(A_780) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1400])).

tff(c_1406,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1402])).

tff(c_1412,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_1406])).

tff(c_1413,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1412])).

tff(c_1418,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1413])).

tff(c_1421,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1418])).

tff(c_1425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1421])).

tff(c_1427,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1413])).

tff(c_1401,plain,(
    ! [A_776,D_777] :
      ( k3_tmap_1(A_776,'#skF_2','#skF_1',D_777,'#skF_3') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_777))
      | ~ m1_pre_topc(D_777,'#skF_1')
      | ~ m1_pre_topc(D_777,A_776)
      | ~ m1_pre_topc('#skF_1',A_776)
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1400])).

tff(c_1440,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1427,c_1401])).

tff(c_1443,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1427,c_1440])).

tff(c_1444,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1443])).

tff(c_1349,plain,(
    ! [A_757,B_758,C_759,D_760] :
      ( k2_partfun1(u1_struct_0(A_757),u1_struct_0(B_758),C_759,u1_struct_0(D_760)) = k2_tmap_1(A_757,B_758,C_759,D_760)
      | ~ m1_pre_topc(D_760,A_757)
      | ~ m1_subset_1(C_759,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_757),u1_struct_0(B_758))))
      | ~ v1_funct_2(C_759,u1_struct_0(A_757),u1_struct_0(B_758))
      | ~ v1_funct_1(C_759)
      | ~ l1_pre_topc(B_758)
      | ~ v2_pre_topc(B_758)
      | v2_struct_0(B_758)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1353,plain,(
    ! [D_760] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_760)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_760)
      | ~ m1_pre_topc(D_760,'#skF_1')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_1349])).

tff(c_1357,plain,(
    ! [D_760] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_760)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_760)
      | ~ m1_pre_topc(D_760,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_1353])).

tff(c_1358,plain,(
    ! [D_760] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',u1_struct_0(D_760)) = k2_tmap_1('#skF_1','#skF_2','#skF_3',D_760)
      | ~ m1_pre_topc(D_760,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_1357])).

tff(c_1496,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1444,c_1358])).

tff(c_1503,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_1496])).

tff(c_1368,plain,(
    ! [C_762,B_763,D_764,A_765] :
      ( r2_funct_2(u1_struct_0(C_762),u1_struct_0(B_763),D_764,k3_tmap_1(A_765,B_763,C_762,C_762,D_764))
      | ~ m1_subset_1(D_764,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_762),u1_struct_0(B_763))))
      | ~ v1_funct_2(D_764,u1_struct_0(C_762),u1_struct_0(B_763))
      | ~ v1_funct_1(D_764)
      | ~ m1_pre_topc(C_762,A_765)
      | v2_struct_0(C_762)
      | ~ l1_pre_topc(B_763)
      | ~ v2_pre_topc(B_763)
      | v2_struct_0(B_763)
      | ~ l1_pre_topc(A_765)
      | ~ v2_pre_topc(A_765)
      | v2_struct_0(A_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_1372,plain,(
    ! [A_765] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_765,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_765)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_765)
      | ~ v2_pre_topc(A_765)
      | v2_struct_0(A_765) ) ),
    inference(resolution,[status(thm)],[c_48,c_1368])).

tff(c_1376,plain,(
    ! [A_765] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_765,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_765)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_765)
      | ~ v2_pre_topc(A_765)
      | v2_struct_0(A_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1372])).

tff(c_1378,plain,(
    ! [A_766] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_1376])).

tff(c_1380,plain,(
    ! [A_766] :
      ( k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_1',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_1378,c_4])).

tff(c_1383,plain,(
    ! [A_766] :
      ( k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
      | ~ m1_subset_1(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_766,'#skF_2','#skF_1','#skF_1','#skF_3'))
      | ~ m1_pre_topc('#skF_1',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1380])).

tff(c_1511,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_3'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_1383])).

tff(c_1518,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1427,c_1503,c_1503,c_1503,c_1511])).

tff(c_1519,plain,
    ( k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1518])).

tff(c_1593,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_1596,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1322,c_1593])).

tff(c_1600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1596])).

tff(c_1601,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_1700,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1601])).

tff(c_1703,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1700])).

tff(c_1707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1323,c_52,c_50,c_48,c_1703])).

tff(c_1708,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1601])).

tff(c_1768,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1708])).

tff(c_1771,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1337,c_1768])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1771])).

tff(c_1776,plain,(
    k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1708])).

tff(c_1560,plain,(
    ! [C_789,A_793,D_788,E_790,B_791,H_792] :
      ( r1_tmap_1(E_790,B_791,k2_tmap_1(A_793,B_791,C_789,E_790),H_792)
      | ~ r1_tmap_1(k1_tsep_1(A_793,D_788,E_790),B_791,k2_tmap_1(A_793,B_791,C_789,k1_tsep_1(A_793,D_788,E_790)),H_792)
      | ~ m1_subset_1(H_792,u1_struct_0(E_790))
      | ~ m1_subset_1(H_792,u1_struct_0(D_788))
      | ~ m1_subset_1(H_792,u1_struct_0(k1_tsep_1(A_793,D_788,E_790)))
      | ~ m1_pre_topc(E_790,A_793)
      | v2_struct_0(E_790)
      | ~ m1_pre_topc(D_788,A_793)
      | v2_struct_0(D_788)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_793),u1_struct_0(B_791))))
      | ~ v1_funct_2(C_789,u1_struct_0(A_793),u1_struct_0(B_791))
      | ~ v1_funct_1(C_789)
      | ~ l1_pre_topc(B_791)
      | ~ v2_pre_topc(B_791)
      | v2_struct_0(B_791)
      | ~ l1_pre_topc(A_793)
      | ~ v2_pre_topc(A_793)
      | v2_struct_0(A_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1562,plain,(
    ! [B_791,C_789,H_792] :
      ( r1_tmap_1('#skF_5',B_791,k2_tmap_1('#skF_1',B_791,C_789,'#skF_5'),H_792)
      | ~ r1_tmap_1('#skF_1',B_791,k2_tmap_1('#skF_1',B_791,C_789,k1_tsep_1('#skF_1','#skF_4','#skF_5')),H_792)
      | ~ m1_subset_1(H_792,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_792,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_792,u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_791))))
      | ~ v1_funct_2(C_789,u1_struct_0('#skF_1'),u1_struct_0(B_791))
      | ~ v1_funct_1(C_789)
      | ~ l1_pre_topc(B_791)
      | ~ v2_pre_topc(B_791)
      | v2_struct_0(B_791)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1560])).

tff(c_1566,plain,(
    ! [B_791,C_789,H_792] :
      ( r1_tmap_1('#skF_5',B_791,k2_tmap_1('#skF_1',B_791,C_789,'#skF_5'),H_792)
      | ~ r1_tmap_1('#skF_1',B_791,k2_tmap_1('#skF_1',B_791,C_789,'#skF_1'),H_792)
      | ~ m1_subset_1(H_792,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_792,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_792,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_791))))
      | ~ v1_funct_2(C_789,u1_struct_0('#skF_1'),u1_struct_0(B_791))
      | ~ v1_funct_1(C_789)
      | ~ l1_pre_topc(B_791)
      | ~ v2_pre_topc(B_791)
      | v2_struct_0(B_791)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_40,c_38,c_38,c_1562])).

tff(c_1749,plain,(
    ! [B_802,C_803,H_804] :
      ( r1_tmap_1('#skF_5',B_802,k2_tmap_1('#skF_1',B_802,C_803,'#skF_5'),H_804)
      | ~ r1_tmap_1('#skF_1',B_802,k2_tmap_1('#skF_1',B_802,C_803,'#skF_1'),H_804)
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_1'))
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_802))))
      | ~ v1_funct_2(C_803,u1_struct_0('#skF_1'),u1_struct_0(B_802))
      | ~ v1_funct_1(C_803)
      | ~ l1_pre_topc(B_802)
      | ~ v2_pre_topc(B_802)
      | v2_struct_0(B_802) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_46,c_42,c_1566])).

tff(c_1756,plain,(
    ! [H_804] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_804)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_804)
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_1'))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1749])).

tff(c_1766,plain,(
    ! [H_804] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_804)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_804)
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1756])).

tff(c_1767,plain,(
    ! [H_804] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_804)
      | ~ r1_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_1'),H_804)
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_804,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1766])).

tff(c_1815,plain,(
    ! [H_805] :
      ( r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),H_805)
      | ~ r1_tmap_1('#skF_1','#skF_2','#skF_3',H_805)
      | ~ m1_subset_1(H_805,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(H_805,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_805,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_1767])).

tff(c_1288,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1818,plain,
    ( ~ r1_tmap_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1815,c_1288])).

tff(c_1822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_84,c_32,c_1287,c_1818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.90  
% 4.72/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.90  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.72/1.90  
% 4.72/1.90  %Foreground sorts:
% 4.72/1.90  
% 4.72/1.90  
% 4.72/1.90  %Background operators:
% 4.72/1.90  
% 4.72/1.90  
% 4.72/1.90  %Foreground operators:
% 4.72/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.72/1.90  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.72/1.90  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.72/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.72/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.90  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.72/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.72/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.72/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.72/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.72/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.72/1.90  tff('#skF_8', type, '#skF_8': $i).
% 4.72/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.90  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.72/1.90  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.72/1.90  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.72/1.90  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.72/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.72/1.90  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.72/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.90  
% 5.08/1.94  tff(f_265, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((A = k1_tsep_1(A, D, E)) => (![F]: (m1_subset_1(F, u1_struct_0(A)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(A, B, C, F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 5.08/1.94  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.08/1.94  tff(f_122, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 5.08/1.94  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.08/1.94  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.08/1.94  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.08/1.94  tff(f_209, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 5.08/1.94  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.08/1.94  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => (![F]: (m1_subset_1(F, u1_struct_0(k1_tsep_1(A, D, E))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(E)) => (((F = G) & (F = H)) => (r1_tmap_1(k1_tsep_1(A, D, E), B, k2_tmap_1(A, B, C, k1_tsep_1(A, D, E)), F) <=> (r1_tmap_1(D, B, k2_tmap_1(A, B, C, D), G) & r1_tmap_1(E, B, k2_tmap_1(A, B, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 5.08/1.94  tff(c_28, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_81, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 5.08/1.94  tff(c_30, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_78, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 5.08/1.94  tff(c_84, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_78])).
% 5.08/1.94  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_76, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_79, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_76])).
% 5.08/1.94  tff(c_85, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_79])).
% 5.08/1.94  tff(c_101, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitLeft, [status(thm)], [c_85])).
% 5.08/1.94  tff(c_72, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_80, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_72])).
% 5.08/1.94  tff(c_100, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_80])).
% 5.08/1.94  tff(c_66, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_77, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 5.08/1.94  tff(c_83, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_77])).
% 5.08/1.94  tff(c_109, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_100, c_83])).
% 5.08/1.94  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_38, plain, (k1_tsep_1('#skF_1', '#skF_4', '#skF_5')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.08/1.94  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_110, plain, (![A_579, B_580, C_581, D_582]: (v1_funct_1(k2_tmap_1(A_579, B_580, C_581, D_582)) | ~l1_struct_0(D_582) | ~m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_579), u1_struct_0(B_580)))) | ~v1_funct_2(C_581, u1_struct_0(A_579), u1_struct_0(B_580)) | ~v1_funct_1(C_581) | ~l1_struct_0(B_580) | ~l1_struct_0(A_579))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_112, plain, (![D_582]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_582)) | ~l1_struct_0(D_582) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_110])).
% 5.08/1.94  tff(c_115, plain, (![D_582]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_582)) | ~l1_struct_0(D_582) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_112])).
% 5.08/1.94  tff(c_116, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_115])).
% 5.08/1.94  tff(c_119, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_116])).
% 5.08/1.94  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_119])).
% 5.08/1.94  tff(c_125, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_115])).
% 5.08/1.94  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_124, plain, (![D_582]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_582)) | ~l1_struct_0(D_582))), inference(splitRight, [status(thm)], [c_115])).
% 5.08/1.94  tff(c_126, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_124])).
% 5.08/1.94  tff(c_129, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_126])).
% 5.08/1.94  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_129])).
% 5.08/1.94  tff(c_135, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_124])).
% 5.08/1.94  tff(c_144, plain, (![A_588, B_589, C_590, D_591]: (v1_funct_2(k2_tmap_1(A_588, B_589, C_590, D_591), u1_struct_0(D_591), u1_struct_0(B_589)) | ~l1_struct_0(D_591) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_588), u1_struct_0(B_589)))) | ~v1_funct_2(C_590, u1_struct_0(A_588), u1_struct_0(B_589)) | ~v1_funct_1(C_590) | ~l1_struct_0(B_589) | ~l1_struct_0(A_588))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_146, plain, (![D_591]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_591), u1_struct_0(D_591), u1_struct_0('#skF_2')) | ~l1_struct_0(D_591) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_144])).
% 5.08/1.94  tff(c_149, plain, (![D_591]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_591), u1_struct_0(D_591), u1_struct_0('#skF_2')) | ~l1_struct_0(D_591))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_135, c_52, c_50, c_146])).
% 5.08/1.94  tff(c_12, plain, (![A_52, B_53, C_54, D_55]: (m1_subset_1(k2_tmap_1(A_52, B_53, C_54, D_55), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_55), u1_struct_0(B_53)))) | ~l1_struct_0(D_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52), u1_struct_0(B_53)))) | ~v1_funct_2(C_54, u1_struct_0(A_52), u1_struct_0(B_53)) | ~v1_funct_1(C_54) | ~l1_struct_0(B_53) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_134, plain, (![D_582]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_582)) | ~l1_struct_0(D_582))), inference(splitRight, [status(thm)], [c_124])).
% 5.08/1.94  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_24, plain, (![A_311]: (m1_pre_topc(A_311, A_311) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_179])).
% 5.08/1.94  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 5.08/1.94  tff(c_197, plain, (![C_611, B_612, D_610, E_608, A_609]: (k3_tmap_1(A_609, B_612, C_611, D_610, E_608)=k2_partfun1(u1_struct_0(C_611), u1_struct_0(B_612), E_608, u1_struct_0(D_610)) | ~m1_pre_topc(D_610, C_611) | ~m1_subset_1(E_608, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_611), u1_struct_0(B_612)))) | ~v1_funct_2(E_608, u1_struct_0(C_611), u1_struct_0(B_612)) | ~v1_funct_1(E_608) | ~m1_pre_topc(D_610, A_609) | ~m1_pre_topc(C_611, A_609) | ~l1_pre_topc(B_612) | ~v2_pre_topc(B_612) | v2_struct_0(B_612) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.94  tff(c_201, plain, (![A_609, D_610]: (k3_tmap_1(A_609, '#skF_2', '#skF_1', D_610, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_610, A_609) | ~m1_pre_topc('#skF_1', A_609) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(resolution, [status(thm)], [c_48, c_197])).
% 5.08/1.94  tff(c_205, plain, (![A_609, D_610]: (k3_tmap_1(A_609, '#skF_2', '#skF_1', D_610, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_1') | ~m1_pre_topc(D_610, A_609) | ~m1_pre_topc('#skF_1', A_609) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_201])).
% 5.08/1.94  tff(c_207, plain, (![A_613, D_614]: (k3_tmap_1(A_613, '#skF_2', '#skF_1', D_614, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_614)) | ~m1_pre_topc(D_614, '#skF_1') | ~m1_pre_topc(D_614, A_613) | ~m1_pre_topc('#skF_1', A_613) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(negUnitSimplification, [status(thm)], [c_58, c_205])).
% 5.08/1.94  tff(c_211, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_207])).
% 5.08/1.94  tff(c_217, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_211])).
% 5.08/1.94  tff(c_218, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_217])).
% 5.08/1.94  tff(c_223, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_218])).
% 5.08/1.94  tff(c_226, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_223])).
% 5.08/1.94  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_226])).
% 5.08/1.94  tff(c_232, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 5.08/1.94  tff(c_206, plain, (![A_609, D_610]: (k3_tmap_1(A_609, '#skF_2', '#skF_1', D_610, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_1') | ~m1_pre_topc(D_610, A_609) | ~m1_pre_topc('#skF_1', A_609) | ~l1_pre_topc(A_609) | ~v2_pre_topc(A_609) | v2_struct_0(A_609))), inference(negUnitSimplification, [status(thm)], [c_58, c_205])).
% 5.08/1.94  tff(c_245, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_232, c_206])).
% 5.08/1.94  tff(c_248, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_232, c_245])).
% 5.08/1.94  tff(c_249, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_248])).
% 5.08/1.94  tff(c_161, plain, (![A_597, B_598, C_599, D_600]: (k2_partfun1(u1_struct_0(A_597), u1_struct_0(B_598), C_599, u1_struct_0(D_600))=k2_tmap_1(A_597, B_598, C_599, D_600) | ~m1_pre_topc(D_600, A_597) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_597), u1_struct_0(B_598)))) | ~v1_funct_2(C_599, u1_struct_0(A_597), u1_struct_0(B_598)) | ~v1_funct_1(C_599) | ~l1_pre_topc(B_598) | ~v2_pre_topc(B_598) | v2_struct_0(B_598) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.08/1.94  tff(c_165, plain, (![D_600]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_600))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_600) | ~m1_pre_topc(D_600, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_161])).
% 5.08/1.94  tff(c_169, plain, (![D_600]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_600))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_600) | ~m1_pre_topc(D_600, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_165])).
% 5.08/1.94  tff(c_170, plain, (![D_600]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_600))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_600) | ~m1_pre_topc(D_600, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_169])).
% 5.08/1.94  tff(c_301, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_249, c_170])).
% 5.08/1.94  tff(c_308, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_232, c_301])).
% 5.08/1.94  tff(c_180, plain, (![C_602, B_603, D_604, A_605]: (r2_funct_2(u1_struct_0(C_602), u1_struct_0(B_603), D_604, k3_tmap_1(A_605, B_603, C_602, C_602, D_604)) | ~m1_subset_1(D_604, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_602), u1_struct_0(B_603)))) | ~v1_funct_2(D_604, u1_struct_0(C_602), u1_struct_0(B_603)) | ~v1_funct_1(D_604) | ~m1_pre_topc(C_602, A_605) | v2_struct_0(C_602) | ~l1_pre_topc(B_603) | ~v2_pre_topc(B_603) | v2_struct_0(B_603) | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.08/1.94  tff(c_184, plain, (![A_605]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_605, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_605) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(resolution, [status(thm)], [c_48, c_180])).
% 5.08/1.94  tff(c_188, plain, (![A_605]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_605, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_605) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_605) | ~v2_pre_topc(A_605) | v2_struct_0(A_605))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_184])).
% 5.08/1.94  tff(c_190, plain, (![A_606]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_188])).
% 5.08/1.94  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.08/1.94  tff(c_192, plain, (![A_606]: (k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(resolution, [status(thm)], [c_190, c_4])).
% 5.08/1.94  tff(c_195, plain, (![A_606]: (k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_606, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606) | v2_struct_0(A_606))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_192])).
% 5.08/1.94  tff(c_316, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_308, c_195])).
% 5.08/1.94  tff(c_323, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_232, c_308, c_308, c_308, c_316])).
% 5.08/1.94  tff(c_324, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_323])).
% 5.08/1.94  tff(c_398, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_324])).
% 5.08/1.94  tff(c_401, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_398])).
% 5.08/1.94  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_401])).
% 5.08/1.94  tff(c_406, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_324])).
% 5.08/1.94  tff(c_505, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_406])).
% 5.08/1.94  tff(c_508, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_505])).
% 5.08/1.94  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_135, c_52, c_50, c_48, c_508])).
% 5.08/1.94  tff(c_513, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_406])).
% 5.08/1.94  tff(c_560, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_513])).
% 5.08/1.94  tff(c_563, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_149, c_560])).
% 5.08/1.94  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_563])).
% 5.08/1.94  tff(c_568, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_513])).
% 5.08/1.94  tff(c_468, plain, (![B_631, A_633, H_632, D_628, E_630, C_629]: (r1_tmap_1(k1_tsep_1(A_633, D_628, E_630), B_631, k2_tmap_1(A_633, B_631, C_629, k1_tsep_1(A_633, D_628, E_630)), H_632) | ~r1_tmap_1(E_630, B_631, k2_tmap_1(A_633, B_631, C_629, E_630), H_632) | ~r1_tmap_1(D_628, B_631, k2_tmap_1(A_633, B_631, C_629, D_628), H_632) | ~m1_subset_1(H_632, u1_struct_0(E_630)) | ~m1_subset_1(H_632, u1_struct_0(D_628)) | ~m1_subset_1(H_632, u1_struct_0(k1_tsep_1(A_633, D_628, E_630))) | ~m1_pre_topc(E_630, A_633) | v2_struct_0(E_630) | ~m1_pre_topc(D_628, A_633) | v2_struct_0(D_628) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_633), u1_struct_0(B_631)))) | ~v1_funct_2(C_629, u1_struct_0(A_633), u1_struct_0(B_631)) | ~v1_funct_1(C_629) | ~l1_pre_topc(B_631) | ~v2_pre_topc(B_631) | v2_struct_0(B_631) | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.08/1.94  tff(c_472, plain, (![D_628, E_630, H_632]: (r1_tmap_1(k1_tsep_1('#skF_1', D_628, E_630), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_628, E_630)), H_632) | ~r1_tmap_1(E_630, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_630), H_632) | ~r1_tmap_1(D_628, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628), H_632) | ~m1_subset_1(H_632, u1_struct_0(E_630)) | ~m1_subset_1(H_632, u1_struct_0(D_628)) | ~m1_subset_1(H_632, u1_struct_0(k1_tsep_1('#skF_1', D_628, E_630))) | ~m1_pre_topc(E_630, '#skF_1') | v2_struct_0(E_630) | ~m1_pre_topc(D_628, '#skF_1') | v2_struct_0(D_628) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_468])).
% 5.08/1.94  tff(c_476, plain, (![D_628, E_630, H_632]: (r1_tmap_1(k1_tsep_1('#skF_1', D_628, E_630), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_628, E_630)), H_632) | ~r1_tmap_1(E_630, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_630), H_632) | ~r1_tmap_1(D_628, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_628), H_632) | ~m1_subset_1(H_632, u1_struct_0(E_630)) | ~m1_subset_1(H_632, u1_struct_0(D_628)) | ~m1_subset_1(H_632, u1_struct_0(k1_tsep_1('#skF_1', D_628, E_630))) | ~m1_pre_topc(E_630, '#skF_1') | v2_struct_0(E_630) | ~m1_pre_topc(D_628, '#skF_1') | v2_struct_0(D_628) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_472])).
% 5.08/1.94  tff(c_709, plain, (![D_659, E_660, H_661]: (r1_tmap_1(k1_tsep_1('#skF_1', D_659, E_660), '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', D_659, E_660)), H_661) | ~r1_tmap_1(E_660, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', E_660), H_661) | ~r1_tmap_1(D_659, '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_659), H_661) | ~m1_subset_1(H_661, u1_struct_0(E_660)) | ~m1_subset_1(H_661, u1_struct_0(D_659)) | ~m1_subset_1(H_661, u1_struct_0(k1_tsep_1('#skF_1', D_659, E_660))) | ~m1_pre_topc(E_660, '#skF_1') | v2_struct_0(E_660) | ~m1_pre_topc(D_659, '#skF_1') | v2_struct_0(D_659))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_476])).
% 5.08/1.94  tff(c_716, plain, (![H_661]: (r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_661) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_661) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_661) | ~m1_subset_1(H_661, u1_struct_0('#skF_5')) | ~m1_subset_1(H_661, u1_struct_0('#skF_4')) | ~m1_subset_1(H_661, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_709])).
% 5.08/1.94  tff(c_729, plain, (![H_661]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_661) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_661) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_661) | ~m1_subset_1(H_661, u1_struct_0('#skF_5')) | ~m1_subset_1(H_661, u1_struct_0('#skF_4')) | ~m1_subset_1(H_661, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_568, c_38, c_716])).
% 5.08/1.94  tff(c_734, plain, (![H_662]: (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_662) | ~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_662) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_662) | ~m1_subset_1(H_662, u1_struct_0('#skF_5')) | ~m1_subset_1(H_662, u1_struct_0('#skF_4')) | ~m1_subset_1(H_662, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_42, c_729])).
% 5.08/1.94  tff(c_740, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_100, c_734])).
% 5.08/1.94  tff(c_744, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_84, c_32, c_101, c_740])).
% 5.08/1.94  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_744])).
% 5.08/1.94  tff(c_747, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_85])).
% 5.08/1.94  tff(c_757, plain, (![A_666, B_667, C_668, D_669]: (v1_funct_1(k2_tmap_1(A_666, B_667, C_668, D_669)) | ~l1_struct_0(D_669) | ~m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_666), u1_struct_0(B_667)))) | ~v1_funct_2(C_668, u1_struct_0(A_666), u1_struct_0(B_667)) | ~v1_funct_1(C_668) | ~l1_struct_0(B_667) | ~l1_struct_0(A_666))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_759, plain, (![D_669]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_669)) | ~l1_struct_0(D_669) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_757])).
% 5.08/1.94  tff(c_762, plain, (![D_669]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_669)) | ~l1_struct_0(D_669) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_759])).
% 5.08/1.94  tff(c_763, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_762])).
% 5.08/1.94  tff(c_766, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_763])).
% 5.08/1.94  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_766])).
% 5.08/1.94  tff(c_772, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_762])).
% 5.08/1.94  tff(c_771, plain, (![D_669]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_669)) | ~l1_struct_0(D_669))), inference(splitRight, [status(thm)], [c_762])).
% 5.08/1.94  tff(c_773, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_771])).
% 5.08/1.94  tff(c_776, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_773])).
% 5.08/1.94  tff(c_780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_776])).
% 5.08/1.94  tff(c_782, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_771])).
% 5.08/1.94  tff(c_791, plain, (![A_675, B_676, C_677, D_678]: (v1_funct_2(k2_tmap_1(A_675, B_676, C_677, D_678), u1_struct_0(D_678), u1_struct_0(B_676)) | ~l1_struct_0(D_678) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_675), u1_struct_0(B_676)))) | ~v1_funct_2(C_677, u1_struct_0(A_675), u1_struct_0(B_676)) | ~v1_funct_1(C_677) | ~l1_struct_0(B_676) | ~l1_struct_0(A_675))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_793, plain, (![D_678]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_678), u1_struct_0(D_678), u1_struct_0('#skF_2')) | ~l1_struct_0(D_678) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_791])).
% 5.08/1.94  tff(c_796, plain, (![D_678]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_678), u1_struct_0(D_678), u1_struct_0('#skF_2')) | ~l1_struct_0(D_678))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_782, c_52, c_50, c_793])).
% 5.08/1.94  tff(c_781, plain, (![D_669]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_669)) | ~l1_struct_0(D_669))), inference(splitRight, [status(thm)], [c_771])).
% 5.08/1.94  tff(c_851, plain, (![C_705, E_702, D_704, A_703, B_706]: (k3_tmap_1(A_703, B_706, C_705, D_704, E_702)=k2_partfun1(u1_struct_0(C_705), u1_struct_0(B_706), E_702, u1_struct_0(D_704)) | ~m1_pre_topc(D_704, C_705) | ~m1_subset_1(E_702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_705), u1_struct_0(B_706)))) | ~v1_funct_2(E_702, u1_struct_0(C_705), u1_struct_0(B_706)) | ~v1_funct_1(E_702) | ~m1_pre_topc(D_704, A_703) | ~m1_pre_topc(C_705, A_703) | ~l1_pre_topc(B_706) | ~v2_pre_topc(B_706) | v2_struct_0(B_706) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.94  tff(c_855, plain, (![A_703, D_704]: (k3_tmap_1(A_703, '#skF_2', '#skF_1', D_704, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_704)) | ~m1_pre_topc(D_704, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_704, A_703) | ~m1_pre_topc('#skF_1', A_703) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(resolution, [status(thm)], [c_48, c_851])).
% 5.08/1.94  tff(c_859, plain, (![A_703, D_704]: (k3_tmap_1(A_703, '#skF_2', '#skF_1', D_704, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_704)) | ~m1_pre_topc(D_704, '#skF_1') | ~m1_pre_topc(D_704, A_703) | ~m1_pre_topc('#skF_1', A_703) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_855])).
% 5.08/1.94  tff(c_872, plain, (![A_713, D_714]: (k3_tmap_1(A_713, '#skF_2', '#skF_1', D_714, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_714)) | ~m1_pre_topc(D_714, '#skF_1') | ~m1_pre_topc(D_714, A_713) | ~m1_pre_topc('#skF_1', A_713) | ~l1_pre_topc(A_713) | ~v2_pre_topc(A_713) | v2_struct_0(A_713))), inference(negUnitSimplification, [status(thm)], [c_58, c_859])).
% 5.08/1.94  tff(c_876, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_872])).
% 5.08/1.94  tff(c_882, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_876])).
% 5.08/1.94  tff(c_883, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_882])).
% 5.08/1.94  tff(c_888, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_883])).
% 5.08/1.94  tff(c_891, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_888])).
% 5.08/1.94  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_891])).
% 5.08/1.94  tff(c_897, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_883])).
% 5.08/1.94  tff(c_860, plain, (![A_703, D_704]: (k3_tmap_1(A_703, '#skF_2', '#skF_1', D_704, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_704)) | ~m1_pre_topc(D_704, '#skF_1') | ~m1_pre_topc(D_704, A_703) | ~m1_pre_topc('#skF_1', A_703) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(negUnitSimplification, [status(thm)], [c_58, c_859])).
% 5.08/1.94  tff(c_910, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_897, c_860])).
% 5.08/1.94  tff(c_913, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_897, c_910])).
% 5.08/1.94  tff(c_914, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_913])).
% 5.08/1.94  tff(c_808, plain, (![A_684, B_685, C_686, D_687]: (k2_partfun1(u1_struct_0(A_684), u1_struct_0(B_685), C_686, u1_struct_0(D_687))=k2_tmap_1(A_684, B_685, C_686, D_687) | ~m1_pre_topc(D_687, A_684) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_684), u1_struct_0(B_685)))) | ~v1_funct_2(C_686, u1_struct_0(A_684), u1_struct_0(B_685)) | ~v1_funct_1(C_686) | ~l1_pre_topc(B_685) | ~v2_pre_topc(B_685) | v2_struct_0(B_685) | ~l1_pre_topc(A_684) | ~v2_pre_topc(A_684) | v2_struct_0(A_684))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.08/1.94  tff(c_812, plain, (![D_687]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_687))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_687) | ~m1_pre_topc(D_687, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_808])).
% 5.08/1.94  tff(c_816, plain, (![D_687]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_687))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_687) | ~m1_pre_topc(D_687, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_812])).
% 5.08/1.94  tff(c_817, plain, (![D_687]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_687))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_687) | ~m1_pre_topc(D_687, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_816])).
% 5.08/1.94  tff(c_966, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_914, c_817])).
% 5.08/1.94  tff(c_973, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_966])).
% 5.08/1.94  tff(c_827, plain, (![C_689, B_690, D_691, A_692]: (r2_funct_2(u1_struct_0(C_689), u1_struct_0(B_690), D_691, k3_tmap_1(A_692, B_690, C_689, C_689, D_691)) | ~m1_subset_1(D_691, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_689), u1_struct_0(B_690)))) | ~v1_funct_2(D_691, u1_struct_0(C_689), u1_struct_0(B_690)) | ~v1_funct_1(D_691) | ~m1_pre_topc(C_689, A_692) | v2_struct_0(C_689) | ~l1_pre_topc(B_690) | ~v2_pre_topc(B_690) | v2_struct_0(B_690) | ~l1_pre_topc(A_692) | ~v2_pre_topc(A_692) | v2_struct_0(A_692))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.08/1.94  tff(c_831, plain, (![A_692]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_692, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_692) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_692) | ~v2_pre_topc(A_692) | v2_struct_0(A_692))), inference(resolution, [status(thm)], [c_48, c_827])).
% 5.08/1.94  tff(c_835, plain, (![A_692]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_692, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_692) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_692) | ~v2_pre_topc(A_692) | v2_struct_0(A_692))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_831])).
% 5.08/1.94  tff(c_837, plain, (![A_693]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_693) | ~l1_pre_topc(A_693) | ~v2_pre_topc(A_693) | v2_struct_0(A_693))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_835])).
% 5.08/1.94  tff(c_839, plain, (![A_693]: (k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_693) | ~l1_pre_topc(A_693) | ~v2_pre_topc(A_693) | v2_struct_0(A_693))), inference(resolution, [status(thm)], [c_837, c_4])).
% 5.08/1.94  tff(c_842, plain, (![A_693]: (k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_693, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_693) | ~l1_pre_topc(A_693) | ~v2_pre_topc(A_693) | v2_struct_0(A_693))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_839])).
% 5.08/1.94  tff(c_981, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_973, c_842])).
% 5.08/1.94  tff(c_988, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_897, c_973, c_973, c_973, c_981])).
% 5.08/1.94  tff(c_989, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_988])).
% 5.08/1.94  tff(c_1062, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_989])).
% 5.08/1.94  tff(c_1065, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_781, c_1062])).
% 5.08/1.94  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_1065])).
% 5.08/1.94  tff(c_1070, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_989])).
% 5.08/1.94  tff(c_1172, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1070])).
% 5.08/1.94  tff(c_1175, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1172])).
% 5.08/1.94  tff(c_1179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_782, c_52, c_50, c_48, c_1175])).
% 5.08/1.94  tff(c_1180, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_1070])).
% 5.08/1.94  tff(c_1228, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1180])).
% 5.08/1.94  tff(c_1231, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_796, c_1228])).
% 5.08/1.94  tff(c_1235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_1231])).
% 5.08/1.94  tff(c_1236, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_1180])).
% 5.08/1.94  tff(c_930, plain, (![E_717, C_716, H_719, D_715, B_718, A_720]: (r1_tmap_1(D_715, B_718, k2_tmap_1(A_720, B_718, C_716, D_715), H_719) | ~r1_tmap_1(k1_tsep_1(A_720, D_715, E_717), B_718, k2_tmap_1(A_720, B_718, C_716, k1_tsep_1(A_720, D_715, E_717)), H_719) | ~m1_subset_1(H_719, u1_struct_0(E_717)) | ~m1_subset_1(H_719, u1_struct_0(D_715)) | ~m1_subset_1(H_719, u1_struct_0(k1_tsep_1(A_720, D_715, E_717))) | ~m1_pre_topc(E_717, A_720) | v2_struct_0(E_717) | ~m1_pre_topc(D_715, A_720) | v2_struct_0(D_715) | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_720), u1_struct_0(B_718)))) | ~v1_funct_2(C_716, u1_struct_0(A_720), u1_struct_0(B_718)) | ~v1_funct_1(C_716) | ~l1_pre_topc(B_718) | ~v2_pre_topc(B_718) | v2_struct_0(B_718) | ~l1_pre_topc(A_720) | ~v2_pre_topc(A_720) | v2_struct_0(A_720))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.08/1.94  tff(c_934, plain, (![B_718, C_716, H_719]: (r1_tmap_1('#skF_4', B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_4'), H_719) | ~r1_tmap_1(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'), B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_1'), H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(H_719, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_718)))) | ~v1_funct_2(C_716, u1_struct_0('#skF_1'), u1_struct_0(B_718)) | ~v1_funct_1(C_716) | ~l1_pre_topc(B_718) | ~v2_pre_topc(B_718) | v2_struct_0(B_718) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_930])).
% 5.08/1.94  tff(c_939, plain, (![B_718, C_716, H_719]: (r1_tmap_1('#skF_4', B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_4'), H_719) | ~r1_tmap_1('#skF_1', B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_1'), H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_718)))) | ~v1_funct_2(C_716, u1_struct_0('#skF_1'), u1_struct_0(B_718)) | ~v1_funct_1(C_716) | ~l1_pre_topc(B_718) | ~v2_pre_topc(B_718) | v2_struct_0(B_718) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_38, c_38, c_934])).
% 5.08/1.94  tff(c_940, plain, (![B_718, C_716, H_719]: (r1_tmap_1('#skF_4', B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_4'), H_719) | ~r1_tmap_1('#skF_1', B_718, k2_tmap_1('#skF_1', B_718, C_716, '#skF_1'), H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_718)))) | ~v1_funct_2(C_716, u1_struct_0('#skF_1'), u1_struct_0(B_718)) | ~v1_funct_1(C_716) | ~l1_pre_topc(B_718) | ~v2_pre_topc(B_718) | v2_struct_0(B_718))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_939])).
% 5.08/1.94  tff(c_1248, plain, (![H_719]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_719) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_940])).
% 5.08/1.94  tff(c_1266, plain, (![H_719]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_719) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_719) | ~m1_subset_1(H_719, u1_struct_0('#skF_5')) | ~m1_subset_1(H_719, u1_struct_0('#skF_4')) | ~m1_subset_1(H_719, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_1248])).
% 5.08/1.94  tff(c_1279, plain, (![H_735]: (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), H_735) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_735) | ~m1_subset_1(H_735, u1_struct_0('#skF_5')) | ~m1_subset_1(H_735, u1_struct_0('#skF_4')) | ~m1_subset_1(H_735, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1266])).
% 5.08/1.94  tff(c_748, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_8')), inference(splitRight, [status(thm)], [c_85])).
% 5.08/1.94  tff(c_1282, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1279, c_748])).
% 5.08/1.94  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_84, c_32, c_747, c_1282])).
% 5.08/1.94  tff(c_1287, plain, (r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_80])).
% 5.08/1.94  tff(c_1298, plain, (![A_739, B_740, C_741, D_742]: (v1_funct_1(k2_tmap_1(A_739, B_740, C_741, D_742)) | ~l1_struct_0(D_742) | ~m1_subset_1(C_741, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_739), u1_struct_0(B_740)))) | ~v1_funct_2(C_741, u1_struct_0(A_739), u1_struct_0(B_740)) | ~v1_funct_1(C_741) | ~l1_struct_0(B_740) | ~l1_struct_0(A_739))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_1300, plain, (![D_742]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_742)) | ~l1_struct_0(D_742) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1298])).
% 5.08/1.94  tff(c_1303, plain, (![D_742]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_742)) | ~l1_struct_0(D_742) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1300])).
% 5.08/1.94  tff(c_1304, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1303])).
% 5.08/1.94  tff(c_1307, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_1304])).
% 5.08/1.94  tff(c_1311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1307])).
% 5.08/1.94  tff(c_1313, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1303])).
% 5.08/1.94  tff(c_1312, plain, (![D_742]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_742)) | ~l1_struct_0(D_742))), inference(splitRight, [status(thm)], [c_1303])).
% 5.08/1.94  tff(c_1314, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1312])).
% 5.08/1.94  tff(c_1317, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_1314])).
% 5.08/1.94  tff(c_1321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1317])).
% 5.08/1.94  tff(c_1323, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1312])).
% 5.08/1.94  tff(c_1332, plain, (![A_748, B_749, C_750, D_751]: (v1_funct_2(k2_tmap_1(A_748, B_749, C_750, D_751), u1_struct_0(D_751), u1_struct_0(B_749)) | ~l1_struct_0(D_751) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_748), u1_struct_0(B_749)))) | ~v1_funct_2(C_750, u1_struct_0(A_748), u1_struct_0(B_749)) | ~v1_funct_1(C_750) | ~l1_struct_0(B_749) | ~l1_struct_0(A_748))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.94  tff(c_1334, plain, (![D_751]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_751), u1_struct_0(D_751), u1_struct_0('#skF_2')) | ~l1_struct_0(D_751) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1332])).
% 5.08/1.94  tff(c_1337, plain, (![D_751]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_751), u1_struct_0(D_751), u1_struct_0('#skF_2')) | ~l1_struct_0(D_751))), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1323, c_52, c_50, c_1334])).
% 5.08/1.94  tff(c_1322, plain, (![D_742]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_742)) | ~l1_struct_0(D_742))), inference(splitRight, [status(thm)], [c_1312])).
% 5.08/1.94  tff(c_1392, plain, (![C_778, B_779, E_775, D_777, A_776]: (k3_tmap_1(A_776, B_779, C_778, D_777, E_775)=k2_partfun1(u1_struct_0(C_778), u1_struct_0(B_779), E_775, u1_struct_0(D_777)) | ~m1_pre_topc(D_777, C_778) | ~m1_subset_1(E_775, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_778), u1_struct_0(B_779)))) | ~v1_funct_2(E_775, u1_struct_0(C_778), u1_struct_0(B_779)) | ~v1_funct_1(E_775) | ~m1_pre_topc(D_777, A_776) | ~m1_pre_topc(C_778, A_776) | ~l1_pre_topc(B_779) | ~v2_pre_topc(B_779) | v2_struct_0(B_779) | ~l1_pre_topc(A_776) | ~v2_pre_topc(A_776) | v2_struct_0(A_776))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.08/1.94  tff(c_1396, plain, (![A_776, D_777]: (k3_tmap_1(A_776, '#skF_2', '#skF_1', D_777, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_777)) | ~m1_pre_topc(D_777, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc(D_777, A_776) | ~m1_pre_topc('#skF_1', A_776) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_776) | ~v2_pre_topc(A_776) | v2_struct_0(A_776))), inference(resolution, [status(thm)], [c_48, c_1392])).
% 5.08/1.94  tff(c_1400, plain, (![A_776, D_777]: (k3_tmap_1(A_776, '#skF_2', '#skF_1', D_777, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_777)) | ~m1_pre_topc(D_777, '#skF_1') | ~m1_pre_topc(D_777, A_776) | ~m1_pre_topc('#skF_1', A_776) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_776) | ~v2_pre_topc(A_776) | v2_struct_0(A_776))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1396])).
% 5.08/1.94  tff(c_1402, plain, (![A_780, D_781]: (k3_tmap_1(A_780, '#skF_2', '#skF_1', D_781, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_781)) | ~m1_pre_topc(D_781, '#skF_1') | ~m1_pre_topc(D_781, A_780) | ~m1_pre_topc('#skF_1', A_780) | ~l1_pre_topc(A_780) | ~v2_pre_topc(A_780) | v2_struct_0(A_780))), inference(negUnitSimplification, [status(thm)], [c_58, c_1400])).
% 5.08/1.94  tff(c_1406, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1402])).
% 5.08/1.94  tff(c_1412, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_1406])).
% 5.08/1.94  tff(c_1413, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_1412])).
% 5.08/1.94  tff(c_1418, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1413])).
% 5.08/1.94  tff(c_1421, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1418])).
% 5.08/1.94  tff(c_1425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1421])).
% 5.08/1.94  tff(c_1427, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_1413])).
% 5.08/1.94  tff(c_1401, plain, (![A_776, D_777]: (k3_tmap_1(A_776, '#skF_2', '#skF_1', D_777, '#skF_3')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_777)) | ~m1_pre_topc(D_777, '#skF_1') | ~m1_pre_topc(D_777, A_776) | ~m1_pre_topc('#skF_1', A_776) | ~l1_pre_topc(A_776) | ~v2_pre_topc(A_776) | v2_struct_0(A_776))), inference(negUnitSimplification, [status(thm)], [c_58, c_1400])).
% 5.08/1.94  tff(c_1440, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1427, c_1401])).
% 5.08/1.94  tff(c_1443, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1427, c_1440])).
% 5.08/1.94  tff(c_1444, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1443])).
% 5.08/1.94  tff(c_1349, plain, (![A_757, B_758, C_759, D_760]: (k2_partfun1(u1_struct_0(A_757), u1_struct_0(B_758), C_759, u1_struct_0(D_760))=k2_tmap_1(A_757, B_758, C_759, D_760) | ~m1_pre_topc(D_760, A_757) | ~m1_subset_1(C_759, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_757), u1_struct_0(B_758)))) | ~v1_funct_2(C_759, u1_struct_0(A_757), u1_struct_0(B_758)) | ~v1_funct_1(C_759) | ~l1_pre_topc(B_758) | ~v2_pre_topc(B_758) | v2_struct_0(B_758) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.08/1.94  tff(c_1353, plain, (![D_760]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_760))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_760) | ~m1_pre_topc(D_760, '#skF_1') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_1349])).
% 5.08/1.94  tff(c_1357, plain, (![D_760]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_760))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_760) | ~m1_pre_topc(D_760, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_1353])).
% 5.08/1.94  tff(c_1358, plain, (![D_760]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', u1_struct_0(D_760))=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', D_760) | ~m1_pre_topc(D_760, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_1357])).
% 5.08/1.94  tff(c_1496, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1444, c_1358])).
% 5.08/1.94  tff(c_1503, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1427, c_1496])).
% 5.08/1.94  tff(c_1368, plain, (![C_762, B_763, D_764, A_765]: (r2_funct_2(u1_struct_0(C_762), u1_struct_0(B_763), D_764, k3_tmap_1(A_765, B_763, C_762, C_762, D_764)) | ~m1_subset_1(D_764, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_762), u1_struct_0(B_763)))) | ~v1_funct_2(D_764, u1_struct_0(C_762), u1_struct_0(B_763)) | ~v1_funct_1(D_764) | ~m1_pre_topc(C_762, A_765) | v2_struct_0(C_762) | ~l1_pre_topc(B_763) | ~v2_pre_topc(B_763) | v2_struct_0(B_763) | ~l1_pre_topc(A_765) | ~v2_pre_topc(A_765) | v2_struct_0(A_765))), inference(cnfTransformation, [status(thm)], [f_209])).
% 5.08/1.94  tff(c_1372, plain, (![A_765]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_765, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_765) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_765) | ~v2_pre_topc(A_765) | v2_struct_0(A_765))), inference(resolution, [status(thm)], [c_48, c_1368])).
% 5.08/1.94  tff(c_1376, plain, (![A_765]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_765, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_765) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_765) | ~v2_pre_topc(A_765) | v2_struct_0(A_765))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1372])).
% 5.08/1.94  tff(c_1378, plain, (![A_766]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_1376])).
% 5.08/1.94  tff(c_1380, plain, (![A_766]: (k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_1', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(resolution, [status(thm)], [c_1378, c_4])).
% 5.08/1.94  tff(c_1383, plain, (![A_766]: (k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_766, '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1380])).
% 5.08/1.94  tff(c_1511, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_3')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1503, c_1383])).
% 5.08/1.94  tff(c_1518, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1427, c_1503, c_1503, c_1503, c_1511])).
% 5.08/1.94  tff(c_1519, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3' | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1518])).
% 5.08/1.94  tff(c_1593, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1519])).
% 5.08/1.94  tff(c_1596, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1322, c_1593])).
% 5.08/1.94  tff(c_1600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1596])).
% 5.08/1.94  tff(c_1601, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_1519])).
% 5.08/1.94  tff(c_1700, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1601])).
% 5.08/1.94  tff(c_1703, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1700])).
% 5.08/1.94  tff(c_1707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1323, c_52, c_50, c_48, c_1703])).
% 5.08/1.94  tff(c_1708, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_1601])).
% 5.08/1.94  tff(c_1768, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1708])).
% 5.08/1.94  tff(c_1771, plain, (~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1337, c_1768])).
% 5.08/1.94  tff(c_1775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1771])).
% 5.08/1.94  tff(c_1776, plain, (k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_1708])).
% 5.08/1.94  tff(c_1560, plain, (![C_789, A_793, D_788, E_790, B_791, H_792]: (r1_tmap_1(E_790, B_791, k2_tmap_1(A_793, B_791, C_789, E_790), H_792) | ~r1_tmap_1(k1_tsep_1(A_793, D_788, E_790), B_791, k2_tmap_1(A_793, B_791, C_789, k1_tsep_1(A_793, D_788, E_790)), H_792) | ~m1_subset_1(H_792, u1_struct_0(E_790)) | ~m1_subset_1(H_792, u1_struct_0(D_788)) | ~m1_subset_1(H_792, u1_struct_0(k1_tsep_1(A_793, D_788, E_790))) | ~m1_pre_topc(E_790, A_793) | v2_struct_0(E_790) | ~m1_pre_topc(D_788, A_793) | v2_struct_0(D_788) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_793), u1_struct_0(B_791)))) | ~v1_funct_2(C_789, u1_struct_0(A_793), u1_struct_0(B_791)) | ~v1_funct_1(C_789) | ~l1_pre_topc(B_791) | ~v2_pre_topc(B_791) | v2_struct_0(B_791) | ~l1_pre_topc(A_793) | ~v2_pre_topc(A_793) | v2_struct_0(A_793))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.08/1.94  tff(c_1562, plain, (![B_791, C_789, H_792]: (r1_tmap_1('#skF_5', B_791, k2_tmap_1('#skF_1', B_791, C_789, '#skF_5'), H_792) | ~r1_tmap_1('#skF_1', B_791, k2_tmap_1('#skF_1', B_791, C_789, k1_tsep_1('#skF_1', '#skF_4', '#skF_5')), H_792) | ~m1_subset_1(H_792, u1_struct_0('#skF_5')) | ~m1_subset_1(H_792, u1_struct_0('#skF_4')) | ~m1_subset_1(H_792, u1_struct_0(k1_tsep_1('#skF_1', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_1') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_791)))) | ~v1_funct_2(C_789, u1_struct_0('#skF_1'), u1_struct_0(B_791)) | ~v1_funct_1(C_789) | ~l1_pre_topc(B_791) | ~v2_pre_topc(B_791) | v2_struct_0(B_791) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1560])).
% 5.08/1.94  tff(c_1566, plain, (![B_791, C_789, H_792]: (r1_tmap_1('#skF_5', B_791, k2_tmap_1('#skF_1', B_791, C_789, '#skF_5'), H_792) | ~r1_tmap_1('#skF_1', B_791, k2_tmap_1('#skF_1', B_791, C_789, '#skF_1'), H_792) | ~m1_subset_1(H_792, u1_struct_0('#skF_5')) | ~m1_subset_1(H_792, u1_struct_0('#skF_4')) | ~m1_subset_1(H_792, u1_struct_0('#skF_1')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_791)))) | ~v1_funct_2(C_789, u1_struct_0('#skF_1'), u1_struct_0(B_791)) | ~v1_funct_1(C_789) | ~l1_pre_topc(B_791) | ~v2_pre_topc(B_791) | v2_struct_0(B_791) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_40, c_38, c_38, c_1562])).
% 5.08/1.94  tff(c_1749, plain, (![B_802, C_803, H_804]: (r1_tmap_1('#skF_5', B_802, k2_tmap_1('#skF_1', B_802, C_803, '#skF_5'), H_804) | ~r1_tmap_1('#skF_1', B_802, k2_tmap_1('#skF_1', B_802, C_803, '#skF_1'), H_804) | ~m1_subset_1(H_804, u1_struct_0('#skF_5')) | ~m1_subset_1(H_804, u1_struct_0('#skF_4')) | ~m1_subset_1(H_804, u1_struct_0('#skF_1')) | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_802)))) | ~v1_funct_2(C_803, u1_struct_0('#skF_1'), u1_struct_0(B_802)) | ~v1_funct_1(C_803) | ~l1_pre_topc(B_802) | ~v2_pre_topc(B_802) | v2_struct_0(B_802))), inference(negUnitSimplification, [status(thm)], [c_64, c_46, c_42, c_1566])).
% 5.08/1.94  tff(c_1756, plain, (![H_804]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_804) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_804) | ~m1_subset_1(H_804, u1_struct_0('#skF_5')) | ~m1_subset_1(H_804, u1_struct_0('#skF_4')) | ~m1_subset_1(H_804, u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1749])).
% 5.08/1.94  tff(c_1766, plain, (![H_804]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_804) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_804) | ~m1_subset_1(H_804, u1_struct_0('#skF_5')) | ~m1_subset_1(H_804, u1_struct_0('#skF_4')) | ~m1_subset_1(H_804, u1_struct_0('#skF_1')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1756])).
% 5.08/1.94  tff(c_1767, plain, (![H_804]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_804) | ~r1_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'), H_804) | ~m1_subset_1(H_804, u1_struct_0('#skF_5')) | ~m1_subset_1(H_804, u1_struct_0('#skF_4')) | ~m1_subset_1(H_804, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1766])).
% 5.08/1.94  tff(c_1815, plain, (![H_805]: (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), H_805) | ~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', H_805) | ~m1_subset_1(H_805, u1_struct_0('#skF_5')) | ~m1_subset_1(H_805, u1_struct_0('#skF_4')) | ~m1_subset_1(H_805, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_1767])).
% 5.08/1.94  tff(c_1288, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_80])).
% 5.08/1.94  tff(c_1818, plain, (~r1_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1815, c_1288])).
% 5.08/1.94  tff(c_1822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_84, c_32, c_1287, c_1818])).
% 5.08/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/1.94  
% 5.08/1.94  Inference rules
% 5.08/1.94  ----------------------
% 5.08/1.94  #Ref     : 0
% 5.08/1.94  #Sup     : 330
% 5.08/1.94  #Fact    : 0
% 5.08/1.94  #Define  : 0
% 5.08/1.94  #Split   : 29
% 5.08/1.94  #Chain   : 0
% 5.08/1.94  #Close   : 0
% 5.08/1.94  
% 5.08/1.94  Ordering : KBO
% 5.08/1.94  
% 5.08/1.94  Simplification rules
% 5.08/1.94  ----------------------
% 5.08/1.94  #Subsume      : 31
% 5.08/1.94  #Demod        : 767
% 5.08/1.94  #Tautology    : 170
% 5.08/1.94  #SimpNegUnit  : 100
% 5.08/1.94  #BackRed      : 24
% 5.08/1.94  
% 5.08/1.94  #Partial instantiations: 0
% 5.08/1.94  #Strategies tried      : 1
% 5.08/1.94  
% 5.08/1.94  Timing (in seconds)
% 5.08/1.94  ----------------------
% 5.08/1.94  Preprocessing        : 0.43
% 5.08/1.94  Parsing              : 0.22
% 5.08/1.94  CNF conversion       : 0.07
% 5.08/1.94  Main loop            : 0.63
% 5.08/1.94  Inferencing          : 0.21
% 5.08/1.94  Reduction            : 0.22
% 5.08/1.94  Demodulation         : 0.17
% 5.08/1.94  BG Simplification    : 0.04
% 5.08/1.94  Subsumption          : 0.11
% 5.08/1.94  Abstraction          : 0.03
% 5.08/1.94  MUC search           : 0.00
% 5.08/1.94  Cooper               : 0.00
% 5.08/1.94  Total                : 1.15
% 5.08/1.94  Index Insertion      : 0.00
% 5.08/1.94  Index Deletion       : 0.00
% 5.08/1.94  Index Matching       : 0.00
% 5.08/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
