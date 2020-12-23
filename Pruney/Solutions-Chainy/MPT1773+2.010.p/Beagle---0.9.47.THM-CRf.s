%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 385 expanded)
%              Number of leaves         :   35 ( 168 expanded)
%              Depth                    :   15
%              Number of atoms          :  439 (3570 expanded)
%              Number of equality atoms :   32 ( 179 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_255,negated_conjecture,(
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
                                     => ( ( v3_pre_topc(F,D)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
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
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_197,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_16,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_67,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_24,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_22,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_20,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_68,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_18,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_64,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_113,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_115,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_66])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_92,plain,(
    ! [B_556,A_557] :
      ( v2_pre_topc(B_556)
      | ~ m1_pre_topc(B_556,A_557)
      | ~ l1_pre_topc(A_557)
      | ~ v2_pre_topc(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_110,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_73,plain,(
    ! [B_554,A_555] :
      ( l1_pre_topc(B_554)
      | ~ m1_pre_topc(B_554,A_555)
      | ~ l1_pre_topc(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_89,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_132,plain,(
    ! [B_565,D_563,E_566,C_567,A_564] :
      ( k3_tmap_1(A_564,B_565,C_567,D_563,E_566) = k2_partfun1(u1_struct_0(C_567),u1_struct_0(B_565),E_566,u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,C_567)
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_567),u1_struct_0(B_565))))
      | ~ v1_funct_2(E_566,u1_struct_0(C_567),u1_struct_0(B_565))
      | ~ v1_funct_1(E_566)
      | ~ m1_pre_topc(D_563,A_564)
      | ~ m1_pre_topc(C_567,A_564)
      | ~ l1_pre_topc(B_565)
      | ~ v2_pre_topc(B_565)
      | v2_struct_0(B_565)
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_134,plain,(
    ! [A_564,D_563] :
      ( k3_tmap_1(A_564,'#skF_2','#skF_4',D_563,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_563,A_564)
      | ~ m1_pre_topc('#skF_4',A_564)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_137,plain,(
    ! [A_564,D_563] :
      ( k3_tmap_1(A_564,'#skF_2','#skF_4',D_563,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_563))
      | ~ m1_pre_topc(D_563,'#skF_4')
      | ~ m1_pre_topc(D_563,A_564)
      | ~ m1_pre_topc('#skF_4',A_564)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_134])).

tff(c_146,plain,(
    ! [A_574,D_575] :
      ( k3_tmap_1(A_574,'#skF_2','#skF_4',D_575,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_575))
      | ~ m1_pre_topc(D_575,'#skF_4')
      | ~ m1_pre_topc(D_575,A_574)
      | ~ m1_pre_topc('#skF_4',A_574)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_137])).

tff(c_148,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_146])).

tff(c_155,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_148])).

tff(c_156,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_155])).

tff(c_116,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,(
    ! [D_561] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_561)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_561)
      | ~ m1_pre_topc(D_561,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_121,plain,(
    ! [D_561] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_561)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_561)
      | ~ m1_pre_topc(D_561,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_118])).

tff(c_122,plain,(
    ! [D_561] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_561)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_561)
      | ~ m1_pre_topc(D_561,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_121])).

tff(c_168,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_122])).

tff(c_175,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_168])).

tff(c_180,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_113])).

tff(c_204,plain,(
    ! [G_579,E_581,B_577,D_580,A_576,C_578] :
      ( r1_tmap_1(B_577,A_576,C_578,G_579)
      | ~ r1_tmap_1(D_580,A_576,k2_tmap_1(B_577,A_576,C_578,D_580),G_579)
      | ~ r1_tarski(E_581,u1_struct_0(D_580))
      | ~ r2_hidden(G_579,E_581)
      | ~ v3_pre_topc(E_581,B_577)
      | ~ m1_subset_1(G_579,u1_struct_0(D_580))
      | ~ m1_subset_1(G_579,u1_struct_0(B_577))
      | ~ m1_subset_1(E_581,k1_zfmisc_1(u1_struct_0(B_577)))
      | ~ m1_pre_topc(D_580,B_577)
      | v2_struct_0(D_580)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_577),u1_struct_0(A_576))))
      | ~ v1_funct_2(C_578,u1_struct_0(B_577),u1_struct_0(A_576))
      | ~ v1_funct_1(C_578)
      | ~ l1_pre_topc(B_577)
      | ~ v2_pre_topc(B_577)
      | v2_struct_0(B_577)
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | v2_struct_0(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_206,plain,(
    ! [E_581] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski(E_581,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_581)
      | ~ v3_pre_topc(E_581,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_180,c_204])).

tff(c_209,plain,(
    ! [E_581] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski(E_581,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_581)
      | ~ v3_pre_topc(E_581,'#skF_4')
      | ~ m1_subset_1(E_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_110,c_89,c_36,c_34,c_32,c_30,c_67,c_24,c_206])).

tff(c_211,plain,(
    ! [E_582] :
      ( ~ r1_tarski(E_582,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_582)
      | ~ v3_pre_topc(E_582,'#skF_4')
      | ~ m1_subset_1(E_582,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_44,c_115,c_209])).

tff(c_214,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_211])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68,c_18,c_214])).

tff(c_219,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_239,plain,(
    ! [E_591,A_589,B_590,C_592,D_588] :
      ( k3_tmap_1(A_589,B_590,C_592,D_588,E_591) = k2_partfun1(u1_struct_0(C_592),u1_struct_0(B_590),E_591,u1_struct_0(D_588))
      | ~ m1_pre_topc(D_588,C_592)
      | ~ m1_subset_1(E_591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_592),u1_struct_0(B_590))))
      | ~ v1_funct_2(E_591,u1_struct_0(C_592),u1_struct_0(B_590))
      | ~ v1_funct_1(E_591)
      | ~ m1_pre_topc(D_588,A_589)
      | ~ m1_pre_topc(C_592,A_589)
      | ~ l1_pre_topc(B_590)
      | ~ v2_pre_topc(B_590)
      | v2_struct_0(B_590)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_241,plain,(
    ! [A_589,D_588] :
      ( k3_tmap_1(A_589,'#skF_2','#skF_4',D_588,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_588))
      | ~ m1_pre_topc(D_588,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_588,A_589)
      | ~ m1_pre_topc('#skF_4',A_589)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_244,plain,(
    ! [A_589,D_588] :
      ( k3_tmap_1(A_589,'#skF_2','#skF_4',D_588,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_588))
      | ~ m1_pre_topc(D_588,'#skF_4')
      | ~ m1_pre_topc(D_588,A_589)
      | ~ m1_pre_topc('#skF_4',A_589)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_241])).

tff(c_246,plain,(
    ! [A_593,D_594] :
      ( k3_tmap_1(A_593,'#skF_2','#skF_4',D_594,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_594))
      | ~ m1_pre_topc(D_594,'#skF_4')
      | ~ m1_pre_topc(D_594,A_593)
      | ~ m1_pre_topc('#skF_4',A_593)
      | ~ l1_pre_topc(A_593)
      | ~ v2_pre_topc(A_593)
      | v2_struct_0(A_593) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_244])).

tff(c_248,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_246])).

tff(c_255,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_248])).

tff(c_256,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_255])).

tff(c_223,plain,(
    ! [A_583,B_584,C_585,D_586] :
      ( k2_partfun1(u1_struct_0(A_583),u1_struct_0(B_584),C_585,u1_struct_0(D_586)) = k2_tmap_1(A_583,B_584,C_585,D_586)
      | ~ m1_pre_topc(D_586,A_583)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583),u1_struct_0(B_584))))
      | ~ v1_funct_2(C_585,u1_struct_0(A_583),u1_struct_0(B_584))
      | ~ v1_funct_1(C_585)
      | ~ l1_pre_topc(B_584)
      | ~ v2_pre_topc(B_584)
      | v2_struct_0(B_584)
      | ~ l1_pre_topc(A_583)
      | ~ v2_pre_topc(A_583)
      | v2_struct_0(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_225,plain,(
    ! [D_586] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_586)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_586)
      | ~ m1_pre_topc(D_586,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_223])).

tff(c_228,plain,(
    ! [D_586] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_586)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_586)
      | ~ m1_pre_topc(D_586,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_225])).

tff(c_229,plain,(
    ! [D_586] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_586)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_586)
      | ~ m1_pre_topc(D_586,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_228])).

tff(c_268,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_229])).

tff(c_275,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_268])).

tff(c_279,plain,(
    ! [E_599,A_598,G_595,D_600,C_596,B_597] :
      ( r1_tmap_1(D_600,B_597,k3_tmap_1(A_598,B_597,C_596,D_600,E_599),G_595)
      | ~ r1_tmap_1(C_596,B_597,E_599,G_595)
      | ~ m1_pre_topc(D_600,C_596)
      | ~ m1_subset_1(G_595,u1_struct_0(D_600))
      | ~ m1_subset_1(G_595,u1_struct_0(C_596))
      | ~ m1_subset_1(E_599,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_596),u1_struct_0(B_597))))
      | ~ v1_funct_2(E_599,u1_struct_0(C_596),u1_struct_0(B_597))
      | ~ v1_funct_1(E_599)
      | ~ m1_pre_topc(D_600,A_598)
      | v2_struct_0(D_600)
      | ~ m1_pre_topc(C_596,A_598)
      | v2_struct_0(C_596)
      | ~ l1_pre_topc(B_597)
      | ~ v2_pre_topc(B_597)
      | v2_struct_0(B_597)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_281,plain,(
    ! [D_600,A_598,G_595] :
      ( r1_tmap_1(D_600,'#skF_2',k3_tmap_1(A_598,'#skF_2','#skF_4',D_600,'#skF_5'),G_595)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_595)
      | ~ m1_pre_topc(D_600,'#skF_4')
      | ~ m1_subset_1(G_595,u1_struct_0(D_600))
      | ~ m1_subset_1(G_595,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_600,A_598)
      | v2_struct_0(D_600)
      | ~ m1_pre_topc('#skF_4',A_598)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_32,c_279])).

tff(c_284,plain,(
    ! [D_600,A_598,G_595] :
      ( r1_tmap_1(D_600,'#skF_2',k3_tmap_1(A_598,'#skF_2','#skF_4',D_600,'#skF_5'),G_595)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_595)
      | ~ m1_pre_topc(D_600,'#skF_4')
      | ~ m1_subset_1(G_595,u1_struct_0(D_600))
      | ~ m1_subset_1(G_595,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_600,A_598)
      | v2_struct_0(D_600)
      | ~ m1_pre_topc('#skF_4',A_598)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_281])).

tff(c_311,plain,(
    ! [D_601,A_602,G_603] :
      ( r1_tmap_1(D_601,'#skF_2',k3_tmap_1(A_602,'#skF_2','#skF_4',D_601,'#skF_5'),G_603)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_603)
      | ~ m1_pre_topc(D_601,'#skF_4')
      | ~ m1_subset_1(G_603,u1_struct_0(D_601))
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_601,A_602)
      | v2_struct_0(D_601)
      | ~ m1_pre_topc('#skF_4',A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_284])).

tff(c_314,plain,(
    ! [G_603] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_603)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_603)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_311])).

tff(c_316,plain,(
    ! [G_603] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_603)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_603)
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_42,c_30,c_314])).

tff(c_318,plain,(
    ! [G_604] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_604)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_604)
      | ~ m1_subset_1(G_604,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_604,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_316])).

tff(c_220,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_287,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_220])).

tff(c_321,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_318,c_287])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_24,c_219,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.45  
% 3.08/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.45  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.08/1.45  
% 3.08/1.45  %Foreground sorts:
% 3.08/1.45  
% 3.08/1.45  
% 3.08/1.45  %Background operators:
% 3.08/1.45  
% 3.08/1.45  
% 3.08/1.45  %Foreground operators:
% 3.08/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.45  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.08/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.08/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.45  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.08/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.08/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.45  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.08/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.45  
% 3.08/1.48  tff(f_255, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.08/1.48  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.08/1.48  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.08/1.48  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.08/1.48  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.08/1.48  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.08/1.48  tff(f_197, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.08/1.48  tff(c_16, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_67, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 3.08/1.48  tff(c_24, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_22, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_20, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_68, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 3.08/1.48  tff(c_18, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_64, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_65, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 3.08/1.48  tff(c_113, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_65])).
% 3.08/1.48  tff(c_58, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 3.08/1.48  tff(c_115, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_66])).
% 3.08/1.48  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_92, plain, (![B_556, A_557]: (v2_pre_topc(B_556) | ~m1_pre_topc(B_556, A_557) | ~l1_pre_topc(A_557) | ~v2_pre_topc(A_557))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.48  tff(c_101, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_92])).
% 3.08/1.48  tff(c_110, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 3.08/1.48  tff(c_73, plain, (![B_554, A_555]: (l1_pre_topc(B_554) | ~m1_pre_topc(B_554, A_555) | ~l1_pre_topc(A_555))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.08/1.48  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_73])).
% 3.08/1.48  tff(c_89, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 3.08/1.48  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 3.08/1.48  tff(c_132, plain, (![B_565, D_563, E_566, C_567, A_564]: (k3_tmap_1(A_564, B_565, C_567, D_563, E_566)=k2_partfun1(u1_struct_0(C_567), u1_struct_0(B_565), E_566, u1_struct_0(D_563)) | ~m1_pre_topc(D_563, C_567) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_567), u1_struct_0(B_565)))) | ~v1_funct_2(E_566, u1_struct_0(C_567), u1_struct_0(B_565)) | ~v1_funct_1(E_566) | ~m1_pre_topc(D_563, A_564) | ~m1_pre_topc(C_567, A_564) | ~l1_pre_topc(B_565) | ~v2_pre_topc(B_565) | v2_struct_0(B_565) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.08/1.48  tff(c_134, plain, (![A_564, D_563]: (k3_tmap_1(A_564, '#skF_2', '#skF_4', D_563, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_563)) | ~m1_pre_topc(D_563, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_563, A_564) | ~m1_pre_topc('#skF_4', A_564) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(resolution, [status(thm)], [c_32, c_132])).
% 3.08/1.48  tff(c_137, plain, (![A_564, D_563]: (k3_tmap_1(A_564, '#skF_2', '#skF_4', D_563, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_563)) | ~m1_pre_topc(D_563, '#skF_4') | ~m1_pre_topc(D_563, A_564) | ~m1_pre_topc('#skF_4', A_564) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_134])).
% 3.08/1.48  tff(c_146, plain, (![A_574, D_575]: (k3_tmap_1(A_574, '#skF_2', '#skF_4', D_575, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_575)) | ~m1_pre_topc(D_575, '#skF_4') | ~m1_pre_topc(D_575, A_574) | ~m1_pre_topc('#skF_4', A_574) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(negUnitSimplification, [status(thm)], [c_50, c_137])).
% 3.08/1.48  tff(c_148, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_146])).
% 3.08/1.48  tff(c_155, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_148])).
% 3.08/1.48  tff(c_156, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_155])).
% 3.08/1.48  tff(c_116, plain, (![A_558, B_559, C_560, D_561]: (k2_partfun1(u1_struct_0(A_558), u1_struct_0(B_559), C_560, u1_struct_0(D_561))=k2_tmap_1(A_558, B_559, C_560, D_561) | ~m1_pre_topc(D_561, A_558) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_558), u1_struct_0(B_559)))) | ~v1_funct_2(C_560, u1_struct_0(A_558), u1_struct_0(B_559)) | ~v1_funct_1(C_560) | ~l1_pre_topc(B_559) | ~v2_pre_topc(B_559) | v2_struct_0(B_559) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558) | v2_struct_0(A_558))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.48  tff(c_118, plain, (![D_561]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_561))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_561) | ~m1_pre_topc(D_561, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_116])).
% 3.08/1.48  tff(c_121, plain, (![D_561]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_561))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_561) | ~m1_pre_topc(D_561, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_118])).
% 3.08/1.48  tff(c_122, plain, (![D_561]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_561))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_561) | ~m1_pre_topc(D_561, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_121])).
% 3.08/1.48  tff(c_168, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_156, c_122])).
% 3.08/1.48  tff(c_175, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_168])).
% 3.08/1.48  tff(c_180, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_113])).
% 3.08/1.48  tff(c_204, plain, (![G_579, E_581, B_577, D_580, A_576, C_578]: (r1_tmap_1(B_577, A_576, C_578, G_579) | ~r1_tmap_1(D_580, A_576, k2_tmap_1(B_577, A_576, C_578, D_580), G_579) | ~r1_tarski(E_581, u1_struct_0(D_580)) | ~r2_hidden(G_579, E_581) | ~v3_pre_topc(E_581, B_577) | ~m1_subset_1(G_579, u1_struct_0(D_580)) | ~m1_subset_1(G_579, u1_struct_0(B_577)) | ~m1_subset_1(E_581, k1_zfmisc_1(u1_struct_0(B_577))) | ~m1_pre_topc(D_580, B_577) | v2_struct_0(D_580) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_577), u1_struct_0(A_576)))) | ~v1_funct_2(C_578, u1_struct_0(B_577), u1_struct_0(A_576)) | ~v1_funct_1(C_578) | ~l1_pre_topc(B_577) | ~v2_pre_topc(B_577) | v2_struct_0(B_577) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | v2_struct_0(A_576))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.08/1.48  tff(c_206, plain, (![E_581]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski(E_581, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_581) | ~v3_pre_topc(E_581, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_180, c_204])).
% 3.08/1.48  tff(c_209, plain, (![E_581]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski(E_581, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_581) | ~v3_pre_topc(E_581, '#skF_4') | ~m1_subset_1(E_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_110, c_89, c_36, c_34, c_32, c_30, c_67, c_24, c_206])).
% 3.08/1.48  tff(c_211, plain, (![E_582]: (~r1_tarski(E_582, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_582) | ~v3_pre_topc(E_582, '#skF_4') | ~m1_subset_1(E_582, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_44, c_115, c_209])).
% 3.08/1.48  tff(c_214, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_211])).
% 3.08/1.48  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_68, c_18, c_214])).
% 3.08/1.48  tff(c_219, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_65])).
% 3.08/1.48  tff(c_239, plain, (![E_591, A_589, B_590, C_592, D_588]: (k3_tmap_1(A_589, B_590, C_592, D_588, E_591)=k2_partfun1(u1_struct_0(C_592), u1_struct_0(B_590), E_591, u1_struct_0(D_588)) | ~m1_pre_topc(D_588, C_592) | ~m1_subset_1(E_591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_592), u1_struct_0(B_590)))) | ~v1_funct_2(E_591, u1_struct_0(C_592), u1_struct_0(B_590)) | ~v1_funct_1(E_591) | ~m1_pre_topc(D_588, A_589) | ~m1_pre_topc(C_592, A_589) | ~l1_pre_topc(B_590) | ~v2_pre_topc(B_590) | v2_struct_0(B_590) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.08/1.48  tff(c_241, plain, (![A_589, D_588]: (k3_tmap_1(A_589, '#skF_2', '#skF_4', D_588, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_588)) | ~m1_pre_topc(D_588, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_588, A_589) | ~m1_pre_topc('#skF_4', A_589) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(resolution, [status(thm)], [c_32, c_239])).
% 3.08/1.48  tff(c_244, plain, (![A_589, D_588]: (k3_tmap_1(A_589, '#skF_2', '#skF_4', D_588, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_588)) | ~m1_pre_topc(D_588, '#skF_4') | ~m1_pre_topc(D_588, A_589) | ~m1_pre_topc('#skF_4', A_589) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_241])).
% 3.08/1.48  tff(c_246, plain, (![A_593, D_594]: (k3_tmap_1(A_593, '#skF_2', '#skF_4', D_594, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_594)) | ~m1_pre_topc(D_594, '#skF_4') | ~m1_pre_topc(D_594, A_593) | ~m1_pre_topc('#skF_4', A_593) | ~l1_pre_topc(A_593) | ~v2_pre_topc(A_593) | v2_struct_0(A_593))), inference(negUnitSimplification, [status(thm)], [c_50, c_244])).
% 3.08/1.48  tff(c_248, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_246])).
% 3.08/1.48  tff(c_255, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_248])).
% 3.08/1.48  tff(c_256, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_255])).
% 3.08/1.48  tff(c_223, plain, (![A_583, B_584, C_585, D_586]: (k2_partfun1(u1_struct_0(A_583), u1_struct_0(B_584), C_585, u1_struct_0(D_586))=k2_tmap_1(A_583, B_584, C_585, D_586) | ~m1_pre_topc(D_586, A_583) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_583), u1_struct_0(B_584)))) | ~v1_funct_2(C_585, u1_struct_0(A_583), u1_struct_0(B_584)) | ~v1_funct_1(C_585) | ~l1_pre_topc(B_584) | ~v2_pre_topc(B_584) | v2_struct_0(B_584) | ~l1_pre_topc(A_583) | ~v2_pre_topc(A_583) | v2_struct_0(A_583))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.48  tff(c_225, plain, (![D_586]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_586))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_586) | ~m1_pre_topc(D_586, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_223])).
% 3.08/1.48  tff(c_228, plain, (![D_586]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_586))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_586) | ~m1_pre_topc(D_586, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_225])).
% 3.08/1.48  tff(c_229, plain, (![D_586]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_586))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_586) | ~m1_pre_topc(D_586, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_228])).
% 3.08/1.48  tff(c_268, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_256, c_229])).
% 3.08/1.48  tff(c_275, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_268])).
% 3.08/1.48  tff(c_279, plain, (![E_599, A_598, G_595, D_600, C_596, B_597]: (r1_tmap_1(D_600, B_597, k3_tmap_1(A_598, B_597, C_596, D_600, E_599), G_595) | ~r1_tmap_1(C_596, B_597, E_599, G_595) | ~m1_pre_topc(D_600, C_596) | ~m1_subset_1(G_595, u1_struct_0(D_600)) | ~m1_subset_1(G_595, u1_struct_0(C_596)) | ~m1_subset_1(E_599, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_596), u1_struct_0(B_597)))) | ~v1_funct_2(E_599, u1_struct_0(C_596), u1_struct_0(B_597)) | ~v1_funct_1(E_599) | ~m1_pre_topc(D_600, A_598) | v2_struct_0(D_600) | ~m1_pre_topc(C_596, A_598) | v2_struct_0(C_596) | ~l1_pre_topc(B_597) | ~v2_pre_topc(B_597) | v2_struct_0(B_597) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.08/1.48  tff(c_281, plain, (![D_600, A_598, G_595]: (r1_tmap_1(D_600, '#skF_2', k3_tmap_1(A_598, '#skF_2', '#skF_4', D_600, '#skF_5'), G_595) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_595) | ~m1_pre_topc(D_600, '#skF_4') | ~m1_subset_1(G_595, u1_struct_0(D_600)) | ~m1_subset_1(G_595, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_600, A_598) | v2_struct_0(D_600) | ~m1_pre_topc('#skF_4', A_598) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(resolution, [status(thm)], [c_32, c_279])).
% 3.08/1.48  tff(c_284, plain, (![D_600, A_598, G_595]: (r1_tmap_1(D_600, '#skF_2', k3_tmap_1(A_598, '#skF_2', '#skF_4', D_600, '#skF_5'), G_595) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_595) | ~m1_pre_topc(D_600, '#skF_4') | ~m1_subset_1(G_595, u1_struct_0(D_600)) | ~m1_subset_1(G_595, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_600, A_598) | v2_struct_0(D_600) | ~m1_pre_topc('#skF_4', A_598) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_281])).
% 3.08/1.48  tff(c_311, plain, (![D_601, A_602, G_603]: (r1_tmap_1(D_601, '#skF_2', k3_tmap_1(A_602, '#skF_2', '#skF_4', D_601, '#skF_5'), G_603) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_603) | ~m1_pre_topc(D_601, '#skF_4') | ~m1_subset_1(G_603, u1_struct_0(D_601)) | ~m1_subset_1(G_603, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_601, A_602) | v2_struct_0(D_601) | ~m1_pre_topc('#skF_4', A_602) | ~l1_pre_topc(A_602) | ~v2_pre_topc(A_602) | v2_struct_0(A_602))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_284])).
% 3.08/1.48  tff(c_314, plain, (![G_603]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_603) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_603) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(G_603, u1_struct_0('#skF_3')) | ~m1_subset_1(G_603, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_311])).
% 3.08/1.48  tff(c_316, plain, (![G_603]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_603) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_603) | ~m1_subset_1(G_603, u1_struct_0('#skF_3')) | ~m1_subset_1(G_603, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_42, c_30, c_314])).
% 3.08/1.48  tff(c_318, plain, (![G_604]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_604) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_604) | ~m1_subset_1(G_604, u1_struct_0('#skF_3')) | ~m1_subset_1(G_604, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_316])).
% 3.08/1.48  tff(c_220, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_65])).
% 3.08/1.48  tff(c_287, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_220])).
% 3.08/1.48  tff(c_321, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_318, c_287])).
% 3.08/1.48  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_24, c_219, c_321])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 48
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 3
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 3
% 3.08/1.48  #Demod        : 102
% 3.08/1.48  #Tautology    : 28
% 3.08/1.48  #SimpNegUnit  : 14
% 3.08/1.48  #BackRed      : 4
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.08/1.48  Preprocessing        : 0.40
% 3.08/1.48  Parsing              : 0.20
% 3.08/1.48  CNF conversion       : 0.06
% 3.08/1.48  Main loop            : 0.25
% 3.26/1.48  Inferencing          : 0.09
% 3.26/1.48  Reduction            : 0.09
% 3.26/1.48  Demodulation         : 0.07
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.04
% 3.26/1.48  Abstraction          : 0.01
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.70
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
