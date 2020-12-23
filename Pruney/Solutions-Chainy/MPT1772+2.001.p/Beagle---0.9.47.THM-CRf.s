%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 438 expanded)
%              Number of leaves         :   36 ( 187 expanded)
%              Depth                    :   16
%              Number of atoms          :  448 (3798 expanded)
%              Number of equality atoms :   39 ( 217 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_257,negated_conjecture,(
    ~ ! [A] :
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( r1_tarski(F,u1_struct_0(C))
                                          & m1_connsp_2(F,D,G)
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_106,axiom,(
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

tff(f_153,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_201,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_18,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_67,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_26])).

tff(c_24,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_111,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_20,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_68,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_92,plain,(
    ! [B_560,A_561] :
      ( v2_pre_topc(B_560)
      | ~ m1_pre_topc(B_560,A_561)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_110,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_73,plain,(
    ! [B_558,A_559] :
      ( l1_pre_topc(B_558)
      | ~ m1_pre_topc(B_558,A_559)
      | ~ l1_pre_topc(A_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_89,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_115,plain,(
    ! [A_562,B_563,C_564,D_565] :
      ( k2_partfun1(A_562,B_563,C_564,D_565) = k7_relat_1(C_564,D_565)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_562,B_563)))
      | ~ v1_funct_1(C_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [D_565] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_565) = k7_relat_1('#skF_5',D_565)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_120,plain,(
    ! [D_565] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_565) = k7_relat_1('#skF_5',D_565) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_117])).

tff(c_130,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    ! [D_570] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_570)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_570)
      | ~ m1_pre_topc(D_570,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_135,plain,(
    ! [D_570] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_570)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_570)
      | ~ m1_pre_topc(D_570,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_120,c_132])).

tff(c_136,plain,(
    ! [D_570] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_570)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_570)
      | ~ m1_pre_topc(D_570,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_135])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_137,plain,(
    ! [C_573,E_572,A_571,D_574,B_575] :
      ( k3_tmap_1(A_571,B_575,C_573,D_574,E_572) = k2_partfun1(u1_struct_0(C_573),u1_struct_0(B_575),E_572,u1_struct_0(D_574))
      | ~ m1_pre_topc(D_574,C_573)
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_573),u1_struct_0(B_575))))
      | ~ v1_funct_2(E_572,u1_struct_0(C_573),u1_struct_0(B_575))
      | ~ v1_funct_1(E_572)
      | ~ m1_pre_topc(D_574,A_571)
      | ~ m1_pre_topc(C_573,A_571)
      | ~ l1_pre_topc(B_575)
      | ~ v2_pre_topc(B_575)
      | v2_struct_0(B_575)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_139,plain,(
    ! [A_571,D_574] :
      ( k3_tmap_1(A_571,'#skF_2','#skF_4',D_574,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_574))
      | ~ m1_pre_topc(D_574,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_574,A_571)
      | ~ m1_pre_topc('#skF_4',A_571)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_142,plain,(
    ! [D_574,A_571] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_574)) = k3_tmap_1(A_571,'#skF_2','#skF_4',D_574,'#skF_5')
      | ~ m1_pre_topc(D_574,'#skF_4')
      | ~ m1_pre_topc(D_574,A_571)
      | ~ m1_pre_topc('#skF_4',A_571)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_120,c_139])).

tff(c_153,plain,(
    ! [D_577,A_578] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_577)) = k3_tmap_1(A_578,'#skF_2','#skF_4',D_577,'#skF_5')
      | ~ m1_pre_topc(D_577,'#skF_4')
      | ~ m1_pre_topc(D_577,A_578)
      | ~ m1_pre_topc('#skF_4',A_578)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_142])).

tff(c_155,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_153])).

tff(c_162,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_155])).

tff(c_163,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_162])).

tff(c_179,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_163])).

tff(c_185,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_179])).

tff(c_64,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_114,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_188,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_114])).

tff(c_240,plain,(
    ! [D_601,A_603,B_600,C_602,G_599,E_598] :
      ( r1_tmap_1(B_600,A_603,C_602,G_599)
      | ~ r1_tmap_1(D_601,A_603,k2_tmap_1(B_600,A_603,C_602,D_601),G_599)
      | ~ m1_connsp_2(E_598,B_600,G_599)
      | ~ r1_tarski(E_598,u1_struct_0(D_601))
      | ~ m1_subset_1(G_599,u1_struct_0(D_601))
      | ~ m1_subset_1(G_599,u1_struct_0(B_600))
      | ~ m1_subset_1(E_598,k1_zfmisc_1(u1_struct_0(B_600)))
      | ~ m1_pre_topc(D_601,B_600)
      | v2_struct_0(D_601)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_600),u1_struct_0(A_603))))
      | ~ v1_funct_2(C_602,u1_struct_0(B_600),u1_struct_0(A_603))
      | ~ v1_funct_1(C_602)
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc(A_603)
      | ~ v2_pre_topc(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_244,plain,(
    ! [E_598] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_598,'#skF_4','#skF_8')
      | ~ r1_tarski(E_598,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_598,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_188,c_240])).

tff(c_251,plain,(
    ! [E_598] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_598,'#skF_4','#skF_8')
      | ~ r1_tarski(E_598,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_598,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_110,c_89,c_36,c_34,c_32,c_30,c_67,c_24,c_244])).

tff(c_253,plain,(
    ! [E_604] :
      ( ~ m1_connsp_2(E_604,'#skF_4','#skF_8')
      | ~ r1_tarski(E_604,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_604,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_44,c_111,c_251])).

tff(c_256,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68,c_256])).

tff(c_261,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_261])).

tff(c_265,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_269,plain,(
    ! [A_605,B_606,C_607,D_608] :
      ( k2_partfun1(A_605,B_606,C_607,D_608) = k7_relat_1(C_607,D_608)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606)))
      | ~ v1_funct_1(C_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_271,plain,(
    ! [D_608] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_608) = k7_relat_1('#skF_5',D_608)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_269])).

tff(c_274,plain,(
    ! [D_608] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_608) = k7_relat_1('#skF_5',D_608) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_271])).

tff(c_300,plain,(
    ! [E_616,A_615,D_618,B_619,C_617] :
      ( k3_tmap_1(A_615,B_619,C_617,D_618,E_616) = k2_partfun1(u1_struct_0(C_617),u1_struct_0(B_619),E_616,u1_struct_0(D_618))
      | ~ m1_pre_topc(D_618,C_617)
      | ~ m1_subset_1(E_616,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_617),u1_struct_0(B_619))))
      | ~ v1_funct_2(E_616,u1_struct_0(C_617),u1_struct_0(B_619))
      | ~ v1_funct_1(E_616)
      | ~ m1_pre_topc(D_618,A_615)
      | ~ m1_pre_topc(C_617,A_615)
      | ~ l1_pre_topc(B_619)
      | ~ v2_pre_topc(B_619)
      | v2_struct_0(B_619)
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_302,plain,(
    ! [A_615,D_618] :
      ( k3_tmap_1(A_615,'#skF_2','#skF_4',D_618,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_618))
      | ~ m1_pre_topc(D_618,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_618,A_615)
      | ~ m1_pre_topc('#skF_4',A_615)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(resolution,[status(thm)],[c_32,c_300])).

tff(c_305,plain,(
    ! [D_618,A_615] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_618)) = k3_tmap_1(A_615,'#skF_2','#skF_4',D_618,'#skF_5')
      | ~ m1_pre_topc(D_618,'#skF_4')
      | ~ m1_pre_topc(D_618,A_615)
      | ~ m1_pre_topc('#skF_4',A_615)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_274,c_302])).

tff(c_307,plain,(
    ! [D_620,A_621] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_620)) = k3_tmap_1(A_621,'#skF_2','#skF_4',D_620,'#skF_5')
      | ~ m1_pre_topc(D_620,'#skF_4')
      | ~ m1_pre_topc(D_620,A_621)
      | ~ m1_pre_topc('#skF_4',A_621)
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_305])).

tff(c_309,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_307])).

tff(c_316,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_309])).

tff(c_317,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_316])).

tff(c_284,plain,(
    ! [A_610,B_611,C_612,D_613] :
      ( k2_partfun1(u1_struct_0(A_610),u1_struct_0(B_611),C_612,u1_struct_0(D_613)) = k2_tmap_1(A_610,B_611,C_612,D_613)
      | ~ m1_pre_topc(D_613,A_610)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_610),u1_struct_0(B_611))))
      | ~ v1_funct_2(C_612,u1_struct_0(A_610),u1_struct_0(B_611))
      | ~ v1_funct_1(C_612)
      | ~ l1_pre_topc(B_611)
      | ~ v2_pre_topc(B_611)
      | v2_struct_0(B_611)
      | ~ l1_pre_topc(A_610)
      | ~ v2_pre_topc(A_610)
      | v2_struct_0(A_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_286,plain,(
    ! [D_613] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_613)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_613)
      | ~ m1_pre_topc(D_613,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_284])).

tff(c_289,plain,(
    ! [D_613] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_613)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_613)
      | ~ m1_pre_topc(D_613,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_274,c_286])).

tff(c_290,plain,(
    ! [D_613] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_613)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_613)
      | ~ m1_pre_topc(D_613,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_289])).

tff(c_329,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_290])).

tff(c_336,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_329])).

tff(c_365,plain,(
    ! [D_622,G_624,C_627,A_626,E_623,B_625] :
      ( r1_tmap_1(D_622,B_625,k3_tmap_1(A_626,B_625,C_627,D_622,E_623),G_624)
      | ~ r1_tmap_1(C_627,B_625,E_623,G_624)
      | ~ m1_pre_topc(D_622,C_627)
      | ~ m1_subset_1(G_624,u1_struct_0(D_622))
      | ~ m1_subset_1(G_624,u1_struct_0(C_627))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_623,u1_struct_0(C_627),u1_struct_0(B_625))
      | ~ v1_funct_1(E_623)
      | ~ m1_pre_topc(D_622,A_626)
      | v2_struct_0(D_622)
      | ~ m1_pre_topc(C_627,A_626)
      | v2_struct_0(C_627)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_367,plain,(
    ! [D_622,A_626,G_624] :
      ( r1_tmap_1(D_622,'#skF_2',k3_tmap_1(A_626,'#skF_2','#skF_4',D_622,'#skF_5'),G_624)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_624)
      | ~ m1_pre_topc(D_622,'#skF_4')
      | ~ m1_subset_1(G_624,u1_struct_0(D_622))
      | ~ m1_subset_1(G_624,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_622,A_626)
      | v2_struct_0(D_622)
      | ~ m1_pre_topc('#skF_4',A_626)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(resolution,[status(thm)],[c_32,c_365])).

tff(c_370,plain,(
    ! [D_622,A_626,G_624] :
      ( r1_tmap_1(D_622,'#skF_2',k3_tmap_1(A_626,'#skF_2','#skF_4',D_622,'#skF_5'),G_624)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_624)
      | ~ m1_pre_topc(D_622,'#skF_4')
      | ~ m1_subset_1(G_624,u1_struct_0(D_622))
      | ~ m1_subset_1(G_624,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_622,A_626)
      | v2_struct_0(D_622)
      | ~ m1_pre_topc('#skF_4',A_626)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_367])).

tff(c_372,plain,(
    ! [D_628,A_629,G_630] :
      ( r1_tmap_1(D_628,'#skF_2',k3_tmap_1(A_629,'#skF_2','#skF_4',D_628,'#skF_5'),G_630)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_630)
      | ~ m1_pre_topc(D_628,'#skF_4')
      | ~ m1_subset_1(G_630,u1_struct_0(D_628))
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_628,A_629)
      | v2_struct_0(D_628)
      | ~ m1_pre_topc('#skF_4',A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_370])).

tff(c_375,plain,(
    ! [G_630] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_630)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_630)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_372])).

tff(c_377,plain,(
    ! [G_630] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_630)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_630)
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_42,c_30,c_375])).

tff(c_379,plain,(
    ! [G_631] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_631)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_631)
      | ~ m1_subset_1(G_631,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_631,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_377])).

tff(c_264,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_341,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_264])).

tff(c_382,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_379,c_341])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_24,c_265,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.45  
% 3.02/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.45  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.02/1.45  
% 3.02/1.45  %Foreground sorts:
% 3.02/1.45  
% 3.02/1.45  
% 3.02/1.45  %Background operators:
% 3.02/1.45  
% 3.02/1.45  
% 3.02/1.45  %Foreground operators:
% 3.02/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.02/1.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.02/1.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.02/1.45  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.02/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.45  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.02/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.02/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.45  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.02/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.45  
% 3.42/1.48  tff(f_257, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.42/1.48  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.42/1.48  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.42/1.48  tff(f_31, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.42/1.48  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.42/1.48  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.42/1.48  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.42/1.48  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.42/1.48  tff(c_18, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_67, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_26])).
% 3.42/1.48  tff(c_24, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_58, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58])).
% 3.42/1.48  tff(c_111, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 3.42/1.48  tff(c_22, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_20, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_68, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 3.42/1.48  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_92, plain, (![B_560, A_561]: (v2_pre_topc(B_560) | ~m1_pre_topc(B_560, A_561) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.42/1.48  tff(c_101, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_92])).
% 3.42/1.48  tff(c_110, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 3.42/1.48  tff(c_73, plain, (![B_558, A_559]: (l1_pre_topc(B_558) | ~m1_pre_topc(B_558, A_559) | ~l1_pre_topc(A_559))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.42/1.48  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_73])).
% 3.42/1.48  tff(c_89, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 3.42/1.48  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_115, plain, (![A_562, B_563, C_564, D_565]: (k2_partfun1(A_562, B_563, C_564, D_565)=k7_relat_1(C_564, D_565) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_562, B_563))) | ~v1_funct_1(C_564))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.48  tff(c_117, plain, (![D_565]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_565)=k7_relat_1('#skF_5', D_565) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_115])).
% 3.42/1.48  tff(c_120, plain, (![D_565]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_565)=k7_relat_1('#skF_5', D_565))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_117])).
% 3.42/1.48  tff(c_130, plain, (![A_567, B_568, C_569, D_570]: (k2_partfun1(u1_struct_0(A_567), u1_struct_0(B_568), C_569, u1_struct_0(D_570))=k2_tmap_1(A_567, B_568, C_569, D_570) | ~m1_pre_topc(D_570, A_567) | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_567), u1_struct_0(B_568)))) | ~v1_funct_2(C_569, u1_struct_0(A_567), u1_struct_0(B_568)) | ~v1_funct_1(C_569) | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.48  tff(c_132, plain, (![D_570]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_570))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_570) | ~m1_pre_topc(D_570, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_130])).
% 3.42/1.48  tff(c_135, plain, (![D_570]: (k7_relat_1('#skF_5', u1_struct_0(D_570))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_570) | ~m1_pre_topc(D_570, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_120, c_132])).
% 3.42/1.48  tff(c_136, plain, (![D_570]: (k7_relat_1('#skF_5', u1_struct_0(D_570))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_570) | ~m1_pre_topc(D_570, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_135])).
% 3.42/1.48  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_137, plain, (![C_573, E_572, A_571, D_574, B_575]: (k3_tmap_1(A_571, B_575, C_573, D_574, E_572)=k2_partfun1(u1_struct_0(C_573), u1_struct_0(B_575), E_572, u1_struct_0(D_574)) | ~m1_pre_topc(D_574, C_573) | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_573), u1_struct_0(B_575)))) | ~v1_funct_2(E_572, u1_struct_0(C_573), u1_struct_0(B_575)) | ~v1_funct_1(E_572) | ~m1_pre_topc(D_574, A_571) | ~m1_pre_topc(C_573, A_571) | ~l1_pre_topc(B_575) | ~v2_pre_topc(B_575) | v2_struct_0(B_575) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.42/1.48  tff(c_139, plain, (![A_571, D_574]: (k3_tmap_1(A_571, '#skF_2', '#skF_4', D_574, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_574)) | ~m1_pre_topc(D_574, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_574, A_571) | ~m1_pre_topc('#skF_4', A_571) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(resolution, [status(thm)], [c_32, c_137])).
% 3.42/1.48  tff(c_142, plain, (![D_574, A_571]: (k7_relat_1('#skF_5', u1_struct_0(D_574))=k3_tmap_1(A_571, '#skF_2', '#skF_4', D_574, '#skF_5') | ~m1_pre_topc(D_574, '#skF_4') | ~m1_pre_topc(D_574, A_571) | ~m1_pre_topc('#skF_4', A_571) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_120, c_139])).
% 3.42/1.48  tff(c_153, plain, (![D_577, A_578]: (k7_relat_1('#skF_5', u1_struct_0(D_577))=k3_tmap_1(A_578, '#skF_2', '#skF_4', D_577, '#skF_5') | ~m1_pre_topc(D_577, '#skF_4') | ~m1_pre_topc(D_577, A_578) | ~m1_pre_topc('#skF_4', A_578) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(negUnitSimplification, [status(thm)], [c_50, c_142])).
% 3.42/1.48  tff(c_155, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_153])).
% 3.42/1.48  tff(c_162, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_155])).
% 3.42/1.48  tff(c_163, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_162])).
% 3.42/1.48  tff(c_179, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_163])).
% 3.42/1.48  tff(c_185, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_179])).
% 3.42/1.48  tff(c_64, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_257])).
% 3.42/1.48  tff(c_65, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_64])).
% 3.42/1.48  tff(c_114, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_65])).
% 3.42/1.48  tff(c_188, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_114])).
% 3.42/1.48  tff(c_240, plain, (![D_601, A_603, B_600, C_602, G_599, E_598]: (r1_tmap_1(B_600, A_603, C_602, G_599) | ~r1_tmap_1(D_601, A_603, k2_tmap_1(B_600, A_603, C_602, D_601), G_599) | ~m1_connsp_2(E_598, B_600, G_599) | ~r1_tarski(E_598, u1_struct_0(D_601)) | ~m1_subset_1(G_599, u1_struct_0(D_601)) | ~m1_subset_1(G_599, u1_struct_0(B_600)) | ~m1_subset_1(E_598, k1_zfmisc_1(u1_struct_0(B_600))) | ~m1_pre_topc(D_601, B_600) | v2_struct_0(D_601) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_600), u1_struct_0(A_603)))) | ~v1_funct_2(C_602, u1_struct_0(B_600), u1_struct_0(A_603)) | ~v1_funct_1(C_602) | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | ~l1_pre_topc(A_603) | ~v2_pre_topc(A_603) | v2_struct_0(A_603))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.42/1.48  tff(c_244, plain, (![E_598]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_598, '#skF_4', '#skF_8') | ~r1_tarski(E_598, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_598, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_188, c_240])).
% 3.42/1.48  tff(c_251, plain, (![E_598]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_598, '#skF_4', '#skF_8') | ~r1_tarski(E_598, u1_struct_0('#skF_3')) | ~m1_subset_1(E_598, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_110, c_89, c_36, c_34, c_32, c_30, c_67, c_24, c_244])).
% 3.42/1.48  tff(c_253, plain, (![E_604]: (~m1_connsp_2(E_604, '#skF_4', '#skF_8') | ~r1_tarski(E_604, u1_struct_0('#skF_3')) | ~m1_subset_1(E_604, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_44, c_111, c_251])).
% 3.42/1.48  tff(c_256, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_253])).
% 3.42/1.48  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_68, c_256])).
% 3.42/1.48  tff(c_261, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_65])).
% 3.42/1.48  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_261])).
% 3.42/1.48  tff(c_265, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.42/1.48  tff(c_269, plain, (![A_605, B_606, C_607, D_608]: (k2_partfun1(A_605, B_606, C_607, D_608)=k7_relat_1(C_607, D_608) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))) | ~v1_funct_1(C_607))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.48  tff(c_271, plain, (![D_608]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_608)=k7_relat_1('#skF_5', D_608) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_269])).
% 3.42/1.48  tff(c_274, plain, (![D_608]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_608)=k7_relat_1('#skF_5', D_608))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_271])).
% 3.42/1.48  tff(c_300, plain, (![E_616, A_615, D_618, B_619, C_617]: (k3_tmap_1(A_615, B_619, C_617, D_618, E_616)=k2_partfun1(u1_struct_0(C_617), u1_struct_0(B_619), E_616, u1_struct_0(D_618)) | ~m1_pre_topc(D_618, C_617) | ~m1_subset_1(E_616, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_617), u1_struct_0(B_619)))) | ~v1_funct_2(E_616, u1_struct_0(C_617), u1_struct_0(B_619)) | ~v1_funct_1(E_616) | ~m1_pre_topc(D_618, A_615) | ~m1_pre_topc(C_617, A_615) | ~l1_pre_topc(B_619) | ~v2_pre_topc(B_619) | v2_struct_0(B_619) | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.42/1.48  tff(c_302, plain, (![A_615, D_618]: (k3_tmap_1(A_615, '#skF_2', '#skF_4', D_618, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_618)) | ~m1_pre_topc(D_618, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_618, A_615) | ~m1_pre_topc('#skF_4', A_615) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(resolution, [status(thm)], [c_32, c_300])).
% 3.42/1.48  tff(c_305, plain, (![D_618, A_615]: (k7_relat_1('#skF_5', u1_struct_0(D_618))=k3_tmap_1(A_615, '#skF_2', '#skF_4', D_618, '#skF_5') | ~m1_pre_topc(D_618, '#skF_4') | ~m1_pre_topc(D_618, A_615) | ~m1_pre_topc('#skF_4', A_615) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_274, c_302])).
% 3.42/1.48  tff(c_307, plain, (![D_620, A_621]: (k7_relat_1('#skF_5', u1_struct_0(D_620))=k3_tmap_1(A_621, '#skF_2', '#skF_4', D_620, '#skF_5') | ~m1_pre_topc(D_620, '#skF_4') | ~m1_pre_topc(D_620, A_621) | ~m1_pre_topc('#skF_4', A_621) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(negUnitSimplification, [status(thm)], [c_50, c_305])).
% 3.42/1.48  tff(c_309, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_307])).
% 3.42/1.48  tff(c_316, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_309])).
% 3.42/1.48  tff(c_317, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_316])).
% 3.42/1.48  tff(c_284, plain, (![A_610, B_611, C_612, D_613]: (k2_partfun1(u1_struct_0(A_610), u1_struct_0(B_611), C_612, u1_struct_0(D_613))=k2_tmap_1(A_610, B_611, C_612, D_613) | ~m1_pre_topc(D_613, A_610) | ~m1_subset_1(C_612, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_610), u1_struct_0(B_611)))) | ~v1_funct_2(C_612, u1_struct_0(A_610), u1_struct_0(B_611)) | ~v1_funct_1(C_612) | ~l1_pre_topc(B_611) | ~v2_pre_topc(B_611) | v2_struct_0(B_611) | ~l1_pre_topc(A_610) | ~v2_pre_topc(A_610) | v2_struct_0(A_610))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.48  tff(c_286, plain, (![D_613]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_613))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_613) | ~m1_pre_topc(D_613, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_284])).
% 3.42/1.48  tff(c_289, plain, (![D_613]: (k7_relat_1('#skF_5', u1_struct_0(D_613))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_613) | ~m1_pre_topc(D_613, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_274, c_286])).
% 3.42/1.48  tff(c_290, plain, (![D_613]: (k7_relat_1('#skF_5', u1_struct_0(D_613))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_613) | ~m1_pre_topc(D_613, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_289])).
% 3.42/1.48  tff(c_329, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_317, c_290])).
% 3.42/1.48  tff(c_336, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_329])).
% 3.42/1.48  tff(c_365, plain, (![D_622, G_624, C_627, A_626, E_623, B_625]: (r1_tmap_1(D_622, B_625, k3_tmap_1(A_626, B_625, C_627, D_622, E_623), G_624) | ~r1_tmap_1(C_627, B_625, E_623, G_624) | ~m1_pre_topc(D_622, C_627) | ~m1_subset_1(G_624, u1_struct_0(D_622)) | ~m1_subset_1(G_624, u1_struct_0(C_627)) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627), u1_struct_0(B_625)))) | ~v1_funct_2(E_623, u1_struct_0(C_627), u1_struct_0(B_625)) | ~v1_funct_1(E_623) | ~m1_pre_topc(D_622, A_626) | v2_struct_0(D_622) | ~m1_pre_topc(C_627, A_626) | v2_struct_0(C_627) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(cnfTransformation, [status(thm)], [f_201])).
% 3.42/1.48  tff(c_367, plain, (![D_622, A_626, G_624]: (r1_tmap_1(D_622, '#skF_2', k3_tmap_1(A_626, '#skF_2', '#skF_4', D_622, '#skF_5'), G_624) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_624) | ~m1_pre_topc(D_622, '#skF_4') | ~m1_subset_1(G_624, u1_struct_0(D_622)) | ~m1_subset_1(G_624, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_622, A_626) | v2_struct_0(D_622) | ~m1_pre_topc('#skF_4', A_626) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(resolution, [status(thm)], [c_32, c_365])).
% 3.42/1.48  tff(c_370, plain, (![D_622, A_626, G_624]: (r1_tmap_1(D_622, '#skF_2', k3_tmap_1(A_626, '#skF_2', '#skF_4', D_622, '#skF_5'), G_624) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_624) | ~m1_pre_topc(D_622, '#skF_4') | ~m1_subset_1(G_624, u1_struct_0(D_622)) | ~m1_subset_1(G_624, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_622, A_626) | v2_struct_0(D_622) | ~m1_pre_topc('#skF_4', A_626) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_367])).
% 3.42/1.48  tff(c_372, plain, (![D_628, A_629, G_630]: (r1_tmap_1(D_628, '#skF_2', k3_tmap_1(A_629, '#skF_2', '#skF_4', D_628, '#skF_5'), G_630) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_630) | ~m1_pre_topc(D_628, '#skF_4') | ~m1_subset_1(G_630, u1_struct_0(D_628)) | ~m1_subset_1(G_630, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_628, A_629) | v2_struct_0(D_628) | ~m1_pre_topc('#skF_4', A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_370])).
% 3.42/1.48  tff(c_375, plain, (![G_630]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_630) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_630) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(G_630, u1_struct_0('#skF_3')) | ~m1_subset_1(G_630, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_372])).
% 3.42/1.48  tff(c_377, plain, (![G_630]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_630) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_630) | ~m1_subset_1(G_630, u1_struct_0('#skF_3')) | ~m1_subset_1(G_630, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_42, c_30, c_375])).
% 3.42/1.48  tff(c_379, plain, (![G_631]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_631) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_631) | ~m1_subset_1(G_631, u1_struct_0('#skF_3')) | ~m1_subset_1(G_631, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_377])).
% 3.42/1.48  tff(c_264, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.42/1.48  tff(c_341, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_264])).
% 3.42/1.48  tff(c_382, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_379, c_341])).
% 3.42/1.48  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_24, c_265, c_382])).
% 3.42/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.48  
% 3.42/1.48  Inference rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Ref     : 0
% 3.42/1.48  #Sup     : 58
% 3.42/1.48  #Fact    : 0
% 3.42/1.48  #Define  : 0
% 3.42/1.48  #Split   : 4
% 3.42/1.48  #Chain   : 0
% 3.42/1.48  #Close   : 0
% 3.42/1.48  
% 3.42/1.48  Ordering : KBO
% 3.42/1.48  
% 3.42/1.48  Simplification rules
% 3.42/1.48  ----------------------
% 3.42/1.48  #Subsume      : 3
% 3.42/1.48  #Demod        : 129
% 3.42/1.48  #Tautology    : 35
% 3.42/1.48  #SimpNegUnit  : 19
% 3.42/1.48  #BackRed      : 4
% 3.42/1.48  
% 3.42/1.48  #Partial instantiations: 0
% 3.42/1.48  #Strategies tried      : 1
% 3.42/1.48  
% 3.42/1.48  Timing (in seconds)
% 3.42/1.48  ----------------------
% 3.42/1.48  Preprocessing        : 0.41
% 3.42/1.48  Parsing              : 0.20
% 3.42/1.48  CNF conversion       : 0.06
% 3.42/1.48  Main loop            : 0.28
% 3.42/1.48  Inferencing          : 0.10
% 3.42/1.48  Reduction            : 0.10
% 3.42/1.48  Demodulation         : 0.07
% 3.42/1.48  BG Simplification    : 0.02
% 3.42/1.48  Subsumption          : 0.05
% 3.42/1.48  Abstraction          : 0.01
% 3.42/1.48  MUC search           : 0.00
% 3.42/1.48  Cooper               : 0.00
% 3.42/1.48  Total                : 0.74
% 3.42/1.48  Index Insertion      : 0.00
% 3.42/1.48  Index Deletion       : 0.00
% 3.42/1.48  Index Matching       : 0.00
% 3.42/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
