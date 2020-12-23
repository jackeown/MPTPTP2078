%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 331 expanded)
%              Number of leaves         :   42 ( 144 expanded)
%              Depth                    :   14
%              Number of atoms          :  403 (2463 expanded)
%              Number of equality atoms :    6 ( 107 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_303,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_252,axiom,(
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

tff(f_195,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_670,plain,(
    ! [B_694,A_695] :
      ( v2_pre_topc(B_694)
      | ~ m1_pre_topc(B_694,A_695)
      | ~ l1_pre_topc(A_695)
      | ~ v2_pre_topc(A_695) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_673,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_670])).

tff(c_682,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_673])).

tff(c_96,plain,(
    ! [B_548,A_549] :
      ( l1_pre_topc(B_548)
      | ~ m1_pre_topc(B_548,A_549)
      | ~ l1_pre_topc(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_108,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_99])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_89,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_116,plain,(
    ! [B_552,A_553] :
      ( v1_xboole_0(B_552)
      | ~ m1_subset_1(B_552,A_553)
      | ~ v1_xboole_0(A_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_116])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_111,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102])).

tff(c_149,plain,(
    ! [B_560,A_561] :
      ( v2_pre_topc(B_560)
      | ~ m1_pre_topc(B_560,A_561)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_155,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_149])).

tff(c_164,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_155])).

tff(c_52,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_34,plain,(
    ! [B_37,A_35] :
      ( m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_265,plain,(
    ! [B_588,A_589] :
      ( v3_pre_topc(u1_struct_0(B_588),A_589)
      | ~ v1_tsep_1(B_588,A_589)
      | ~ m1_subset_1(u1_struct_0(B_588),k1_zfmisc_1(u1_struct_0(A_589)))
      | ~ m1_pre_topc(B_588,A_589)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_272,plain,(
    ! [B_37,A_35] :
      ( v3_pre_topc(u1_struct_0(B_37),A_35)
      | ~ v1_tsep_1(B_37,A_35)
      | ~ v2_pre_topc(A_35)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_34,c_265])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_87,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_86])).

tff(c_226,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_88,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_229,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_88])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_462,plain,(
    ! [C_641,D_645,A_644,F_640,B_642,E_643,H_639] :
      ( r1_tmap_1(D_645,B_642,E_643,H_639)
      | ~ r1_tmap_1(C_641,B_642,k3_tmap_1(A_644,B_642,D_645,C_641,E_643),H_639)
      | ~ r1_tarski(F_640,u1_struct_0(C_641))
      | ~ r2_hidden(H_639,F_640)
      | ~ v3_pre_topc(F_640,D_645)
      | ~ m1_subset_1(H_639,u1_struct_0(C_641))
      | ~ m1_subset_1(H_639,u1_struct_0(D_645))
      | ~ m1_subset_1(F_640,k1_zfmisc_1(u1_struct_0(D_645)))
      | ~ m1_pre_topc(C_641,D_645)
      | ~ m1_subset_1(E_643,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_645),u1_struct_0(B_642))))
      | ~ v1_funct_2(E_643,u1_struct_0(D_645),u1_struct_0(B_642))
      | ~ v1_funct_1(E_643)
      | ~ m1_pre_topc(D_645,A_644)
      | v2_struct_0(D_645)
      | ~ m1_pre_topc(C_641,A_644)
      | v2_struct_0(C_641)
      | ~ l1_pre_topc(B_642)
      | ~ v2_pre_topc(B_642)
      | v2_struct_0(B_642)
      | ~ l1_pre_topc(A_644)
      | ~ v2_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_464,plain,(
    ! [F_640] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_640,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_640)
      | ~ v3_pre_topc(F_640,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_640,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_226,c_462])).

tff(c_467,plain,(
    ! [F_640] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_640,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_640)
      | ~ v3_pre_topc(F_640,'#skF_5')
      | ~ m1_subset_1(F_640,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_56,c_54,c_50,c_89,c_46,c_464])).

tff(c_470,plain,(
    ! [F_646] :
      ( ~ r1_tarski(F_646,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_646)
      | ~ v3_pre_topc(F_646,'#skF_5')
      | ~ m1_subset_1(F_646,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_229,c_467])).

tff(c_478,plain,(
    ! [B_37] :
      ( ~ r1_tarski(u1_struct_0(B_37),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_37))
      | ~ v3_pre_topc(u1_struct_0(B_37),'#skF_5')
      | ~ m1_pre_topc(B_37,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_470])).

tff(c_491,plain,(
    ! [B_647] :
      ( ~ r1_tarski(u1_struct_0(B_647),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_647))
      | ~ v3_pre_topc(u1_struct_0(B_647),'#skF_5')
      | ~ m1_pre_topc(B_647,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_478])).

tff(c_495,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_491])).

tff(c_498,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_495])).

tff(c_499,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_502,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_272,c_499])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50,c_164,c_52,c_502])).

tff(c_507,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_517,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_507])).

tff(c_520,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_517])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_520])).

tff(c_523,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_606,plain,(
    ! [D_678,A_679,C_681,E_680,G_677,B_682] :
      ( r1_tmap_1(D_678,B_682,k3_tmap_1(A_679,B_682,C_681,D_678,E_680),G_677)
      | ~ r1_tmap_1(C_681,B_682,E_680,G_677)
      | ~ m1_pre_topc(D_678,C_681)
      | ~ m1_subset_1(G_677,u1_struct_0(D_678))
      | ~ m1_subset_1(G_677,u1_struct_0(C_681))
      | ~ m1_subset_1(E_680,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_681),u1_struct_0(B_682))))
      | ~ v1_funct_2(E_680,u1_struct_0(C_681),u1_struct_0(B_682))
      | ~ v1_funct_1(E_680)
      | ~ m1_pre_topc(D_678,A_679)
      | v2_struct_0(D_678)
      | ~ m1_pre_topc(C_681,A_679)
      | v2_struct_0(C_681)
      | ~ l1_pre_topc(B_682)
      | ~ v2_pre_topc(B_682)
      | v2_struct_0(B_682)
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679)
      | v2_struct_0(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_611,plain,(
    ! [D_678,A_679,G_677] :
      ( r1_tmap_1(D_678,'#skF_3',k3_tmap_1(A_679,'#skF_3','#skF_5',D_678,'#skF_6'),G_677)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_677)
      | ~ m1_pre_topc(D_678,'#skF_5')
      | ~ m1_subset_1(G_677,u1_struct_0(D_678))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_678,A_679)
      | v2_struct_0(D_678)
      | ~ m1_pre_topc('#skF_5',A_679)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679)
      | v2_struct_0(A_679) ) ),
    inference(resolution,[status(thm)],[c_54,c_606])).

tff(c_615,plain,(
    ! [D_678,A_679,G_677] :
      ( r1_tmap_1(D_678,'#skF_3',k3_tmap_1(A_679,'#skF_3','#skF_5',D_678,'#skF_6'),G_677)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_677)
      | ~ m1_pre_topc(D_678,'#skF_5')
      | ~ m1_subset_1(G_677,u1_struct_0(D_678))
      | ~ m1_subset_1(G_677,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_678,A_679)
      | v2_struct_0(D_678)
      | ~ m1_pre_topc('#skF_5',A_679)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679)
      | v2_struct_0(A_679) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_611])).

tff(c_647,plain,(
    ! [D_687,A_688,G_689] :
      ( r1_tmap_1(D_687,'#skF_3',k3_tmap_1(A_688,'#skF_3','#skF_5',D_687,'#skF_6'),G_689)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_689)
      | ~ m1_pre_topc(D_687,'#skF_5')
      | ~ m1_subset_1(G_689,u1_struct_0(D_687))
      | ~ m1_subset_1(G_689,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_687,A_688)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc('#skF_5',A_688)
      | ~ l1_pre_topc(A_688)
      | ~ v2_pre_topc(A_688)
      | v2_struct_0(A_688) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_615])).

tff(c_524,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_650,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_647,c_524])).

tff(c_653,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_64,c_89,c_46,c_50,c_523,c_650])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_653])).

tff(c_657,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_connsp_2('#skF_1'(A_18,B_19),A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_808,plain,(
    ! [C_721,A_722,B_723] :
      ( m1_subset_1(C_721,k1_zfmisc_1(u1_struct_0(A_722)))
      | ~ m1_connsp_2(C_721,A_722,B_723)
      | ~ m1_subset_1(B_723,u1_struct_0(A_722))
      | ~ l1_pre_topc(A_722)
      | ~ v2_pre_topc(A_722)
      | v2_struct_0(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_811,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1('#skF_1'(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_808])).

tff(c_851,plain,(
    ! [C_739,B_740,A_741] :
      ( r2_hidden(C_739,B_740)
      | ~ m1_connsp_2(B_740,A_741,C_739)
      | ~ m1_subset_1(C_739,u1_struct_0(A_741))
      | ~ m1_subset_1(B_740,k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ l1_pre_topc(A_741)
      | ~ v2_pre_topc(A_741)
      | v2_struct_0(A_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_855,plain,(
    ! [B_742,A_743] :
      ( r2_hidden(B_742,'#skF_1'(A_743,B_742))
      | ~ m1_subset_1('#skF_1'(A_743,B_742),k1_zfmisc_1(u1_struct_0(A_743)))
      | ~ m1_subset_1(B_742,u1_struct_0(A_743))
      | ~ l1_pre_topc(A_743)
      | ~ v2_pre_topc(A_743)
      | v2_struct_0(A_743) ) ),
    inference(resolution,[status(thm)],[c_24,c_851])).

tff(c_863,plain,(
    ! [B_744,A_745] :
      ( r2_hidden(B_744,'#skF_1'(A_745,B_744))
      | ~ m1_subset_1(B_744,u1_struct_0(A_745))
      | ~ l1_pre_topc(A_745)
      | ~ v2_pre_topc(A_745)
      | v2_struct_0(A_745) ) ),
    inference(resolution,[status(thm)],[c_811,c_855])).

tff(c_812,plain,(
    ! [A_724,B_725] :
      ( m1_subset_1('#skF_1'(A_724,B_725),k1_zfmisc_1(u1_struct_0(A_724)))
      | ~ m1_subset_1(B_725,u1_struct_0(A_724))
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_24,c_808])).

tff(c_16,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_818,plain,(
    ! [A_724,A_5,B_725] :
      ( ~ v1_xboole_0(u1_struct_0(A_724))
      | ~ r2_hidden(A_5,'#skF_1'(A_724,B_725))
      | ~ m1_subset_1(B_725,u1_struct_0(A_724))
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_812,c_16])).

tff(c_872,plain,(
    ! [A_746,B_747] :
      ( ~ v1_xboole_0(u1_struct_0(A_746))
      | ~ m1_subset_1(B_747,u1_struct_0(A_746))
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746)
      | v2_struct_0(A_746) ) ),
    inference(resolution,[status(thm)],[c_863,c_818])).

tff(c_882,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_872])).

tff(c_890,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_108,c_657,c_882])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.59  
% 3.59/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.59/1.59  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.59/1.59  
% 3.59/1.59  %Foreground sorts:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Background operators:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Foreground operators:
% 3.59/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.59/1.59  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.59/1.59  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.59/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.59/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.59/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.59/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.59/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.59/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.59  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.59/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.59/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.59/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.59/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.59/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.59  
% 3.90/1.62  tff(f_303, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.90/1.62  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.90/1.62  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.90/1.62  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.90/1.62  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.90/1.62  tff(f_128, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.90/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.90/1.62  tff(f_252, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.90/1.62  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.90/1.62  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.90/1.62  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.90/1.62  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.90/1.62  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.90/1.62  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_670, plain, (![B_694, A_695]: (v2_pre_topc(B_694) | ~m1_pre_topc(B_694, A_695) | ~l1_pre_topc(A_695) | ~v2_pre_topc(A_695))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.90/1.62  tff(c_673, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_670])).
% 3.90/1.62  tff(c_682, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_673])).
% 3.90/1.62  tff(c_96, plain, (![B_548, A_549]: (l1_pre_topc(B_548) | ~m1_pre_topc(B_548, A_549) | ~l1_pre_topc(A_549))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.90/1.62  tff(c_99, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_96])).
% 3.90/1.62  tff(c_108, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_99])).
% 3.90/1.62  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_89, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_48])).
% 3.90/1.62  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_116, plain, (![B_552, A_553]: (v1_xboole_0(B_552) | ~m1_subset_1(B_552, A_553) | ~v1_xboole_0(A_553))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.90/1.62  tff(c_132, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_116])).
% 3.90/1.62  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_132])).
% 3.90/1.62  tff(c_10, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.90/1.62  tff(c_102, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_96])).
% 3.90/1.62  tff(c_111, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102])).
% 3.90/1.62  tff(c_149, plain, (![B_560, A_561]: (v2_pre_topc(B_560) | ~m1_pre_topc(B_560, A_561) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.90/1.62  tff(c_155, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_149])).
% 3.90/1.62  tff(c_164, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_155])).
% 3.90/1.62  tff(c_52, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_34, plain, (![B_37, A_35]: (m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.90/1.62  tff(c_265, plain, (![B_588, A_589]: (v3_pre_topc(u1_struct_0(B_588), A_589) | ~v1_tsep_1(B_588, A_589) | ~m1_subset_1(u1_struct_0(B_588), k1_zfmisc_1(u1_struct_0(A_589))) | ~m1_pre_topc(B_588, A_589) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.90/1.62  tff(c_272, plain, (![B_37, A_35]: (v3_pre_topc(u1_struct_0(B_37), A_35) | ~v1_tsep_1(B_37, A_35) | ~v2_pre_topc(A_35) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_34, c_265])).
% 3.90/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.62  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_86, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_87, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_86])).
% 3.90/1.62  tff(c_226, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 3.90/1.62  tff(c_80, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_88, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 3.90/1.62  tff(c_229, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_88])).
% 3.90/1.62  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_303])).
% 3.90/1.62  tff(c_462, plain, (![C_641, D_645, A_644, F_640, B_642, E_643, H_639]: (r1_tmap_1(D_645, B_642, E_643, H_639) | ~r1_tmap_1(C_641, B_642, k3_tmap_1(A_644, B_642, D_645, C_641, E_643), H_639) | ~r1_tarski(F_640, u1_struct_0(C_641)) | ~r2_hidden(H_639, F_640) | ~v3_pre_topc(F_640, D_645) | ~m1_subset_1(H_639, u1_struct_0(C_641)) | ~m1_subset_1(H_639, u1_struct_0(D_645)) | ~m1_subset_1(F_640, k1_zfmisc_1(u1_struct_0(D_645))) | ~m1_pre_topc(C_641, D_645) | ~m1_subset_1(E_643, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_645), u1_struct_0(B_642)))) | ~v1_funct_2(E_643, u1_struct_0(D_645), u1_struct_0(B_642)) | ~v1_funct_1(E_643) | ~m1_pre_topc(D_645, A_644) | v2_struct_0(D_645) | ~m1_pre_topc(C_641, A_644) | v2_struct_0(C_641) | ~l1_pre_topc(B_642) | ~v2_pre_topc(B_642) | v2_struct_0(B_642) | ~l1_pre_topc(A_644) | ~v2_pre_topc(A_644) | v2_struct_0(A_644))), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.90/1.62  tff(c_464, plain, (![F_640]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_640, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_640) | ~v3_pre_topc(F_640, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_640, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_226, c_462])).
% 3.90/1.62  tff(c_467, plain, (![F_640]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_640, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_640) | ~v3_pre_topc(F_640, '#skF_5') | ~m1_subset_1(F_640, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_56, c_54, c_50, c_89, c_46, c_464])).
% 3.90/1.62  tff(c_470, plain, (![F_646]: (~r1_tarski(F_646, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_646) | ~v3_pre_topc(F_646, '#skF_5') | ~m1_subset_1(F_646, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_229, c_467])).
% 3.90/1.62  tff(c_478, plain, (![B_37]: (~r1_tarski(u1_struct_0(B_37), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', u1_struct_0(B_37)) | ~v3_pre_topc(u1_struct_0(B_37), '#skF_5') | ~m1_pre_topc(B_37, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_470])).
% 3.90/1.62  tff(c_491, plain, (![B_647]: (~r1_tarski(u1_struct_0(B_647), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', u1_struct_0(B_647)) | ~v3_pre_topc(u1_struct_0(B_647), '#skF_5') | ~m1_pre_topc(B_647, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_478])).
% 3.90/1.62  tff(c_495, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_491])).
% 3.90/1.62  tff(c_498, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_495])).
% 3.90/1.62  tff(c_499, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_498])).
% 3.90/1.62  tff(c_502, plain, (~v1_tsep_1('#skF_4', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_272, c_499])).
% 3.90/1.62  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_50, c_164, c_52, c_502])).
% 3.90/1.62  tff(c_507, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_498])).
% 3.90/1.62  tff(c_517, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_507])).
% 3.90/1.62  tff(c_520, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_517])).
% 3.90/1.62  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_520])).
% 3.90/1.62  tff(c_523, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 3.90/1.62  tff(c_606, plain, (![D_678, A_679, C_681, E_680, G_677, B_682]: (r1_tmap_1(D_678, B_682, k3_tmap_1(A_679, B_682, C_681, D_678, E_680), G_677) | ~r1_tmap_1(C_681, B_682, E_680, G_677) | ~m1_pre_topc(D_678, C_681) | ~m1_subset_1(G_677, u1_struct_0(D_678)) | ~m1_subset_1(G_677, u1_struct_0(C_681)) | ~m1_subset_1(E_680, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_681), u1_struct_0(B_682)))) | ~v1_funct_2(E_680, u1_struct_0(C_681), u1_struct_0(B_682)) | ~v1_funct_1(E_680) | ~m1_pre_topc(D_678, A_679) | v2_struct_0(D_678) | ~m1_pre_topc(C_681, A_679) | v2_struct_0(C_681) | ~l1_pre_topc(B_682) | ~v2_pre_topc(B_682) | v2_struct_0(B_682) | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679) | v2_struct_0(A_679))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.90/1.62  tff(c_611, plain, (![D_678, A_679, G_677]: (r1_tmap_1(D_678, '#skF_3', k3_tmap_1(A_679, '#skF_3', '#skF_5', D_678, '#skF_6'), G_677) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_677) | ~m1_pre_topc(D_678, '#skF_5') | ~m1_subset_1(G_677, u1_struct_0(D_678)) | ~m1_subset_1(G_677, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_678, A_679) | v2_struct_0(D_678) | ~m1_pre_topc('#skF_5', A_679) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679) | v2_struct_0(A_679))), inference(resolution, [status(thm)], [c_54, c_606])).
% 3.90/1.62  tff(c_615, plain, (![D_678, A_679, G_677]: (r1_tmap_1(D_678, '#skF_3', k3_tmap_1(A_679, '#skF_3', '#skF_5', D_678, '#skF_6'), G_677) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_677) | ~m1_pre_topc(D_678, '#skF_5') | ~m1_subset_1(G_677, u1_struct_0(D_678)) | ~m1_subset_1(G_677, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_678, A_679) | v2_struct_0(D_678) | ~m1_pre_topc('#skF_5', A_679) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679) | v2_struct_0(A_679))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_611])).
% 3.90/1.62  tff(c_647, plain, (![D_687, A_688, G_689]: (r1_tmap_1(D_687, '#skF_3', k3_tmap_1(A_688, '#skF_3', '#skF_5', D_687, '#skF_6'), G_689) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_689) | ~m1_pre_topc(D_687, '#skF_5') | ~m1_subset_1(G_689, u1_struct_0(D_687)) | ~m1_subset_1(G_689, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_687, A_688) | v2_struct_0(D_687) | ~m1_pre_topc('#skF_5', A_688) | ~l1_pre_topc(A_688) | ~v2_pre_topc(A_688) | v2_struct_0(A_688))), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_615])).
% 3.90/1.62  tff(c_524, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 3.90/1.62  tff(c_650, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_647, c_524])).
% 3.90/1.62  tff(c_653, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_64, c_89, c_46, c_50, c_523, c_650])).
% 3.90/1.62  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_653])).
% 3.90/1.62  tff(c_657, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_132])).
% 3.90/1.62  tff(c_24, plain, (![A_18, B_19]: (m1_connsp_2('#skF_1'(A_18, B_19), A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.90/1.62  tff(c_808, plain, (![C_721, A_722, B_723]: (m1_subset_1(C_721, k1_zfmisc_1(u1_struct_0(A_722))) | ~m1_connsp_2(C_721, A_722, B_723) | ~m1_subset_1(B_723, u1_struct_0(A_722)) | ~l1_pre_topc(A_722) | ~v2_pre_topc(A_722) | v2_struct_0(A_722))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.90/1.62  tff(c_811, plain, (![A_18, B_19]: (m1_subset_1('#skF_1'(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(resolution, [status(thm)], [c_24, c_808])).
% 3.90/1.62  tff(c_851, plain, (![C_739, B_740, A_741]: (r2_hidden(C_739, B_740) | ~m1_connsp_2(B_740, A_741, C_739) | ~m1_subset_1(C_739, u1_struct_0(A_741)) | ~m1_subset_1(B_740, k1_zfmisc_1(u1_struct_0(A_741))) | ~l1_pre_topc(A_741) | ~v2_pre_topc(A_741) | v2_struct_0(A_741))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.90/1.62  tff(c_855, plain, (![B_742, A_743]: (r2_hidden(B_742, '#skF_1'(A_743, B_742)) | ~m1_subset_1('#skF_1'(A_743, B_742), k1_zfmisc_1(u1_struct_0(A_743))) | ~m1_subset_1(B_742, u1_struct_0(A_743)) | ~l1_pre_topc(A_743) | ~v2_pre_topc(A_743) | v2_struct_0(A_743))), inference(resolution, [status(thm)], [c_24, c_851])).
% 3.90/1.62  tff(c_863, plain, (![B_744, A_745]: (r2_hidden(B_744, '#skF_1'(A_745, B_744)) | ~m1_subset_1(B_744, u1_struct_0(A_745)) | ~l1_pre_topc(A_745) | ~v2_pre_topc(A_745) | v2_struct_0(A_745))), inference(resolution, [status(thm)], [c_811, c_855])).
% 3.90/1.62  tff(c_812, plain, (![A_724, B_725]: (m1_subset_1('#skF_1'(A_724, B_725), k1_zfmisc_1(u1_struct_0(A_724))) | ~m1_subset_1(B_725, u1_struct_0(A_724)) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(resolution, [status(thm)], [c_24, c_808])).
% 3.90/1.62  tff(c_16, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.90/1.62  tff(c_818, plain, (![A_724, A_5, B_725]: (~v1_xboole_0(u1_struct_0(A_724)) | ~r2_hidden(A_5, '#skF_1'(A_724, B_725)) | ~m1_subset_1(B_725, u1_struct_0(A_724)) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(resolution, [status(thm)], [c_812, c_16])).
% 3.90/1.62  tff(c_872, plain, (![A_746, B_747]: (~v1_xboole_0(u1_struct_0(A_746)) | ~m1_subset_1(B_747, u1_struct_0(A_746)) | ~l1_pre_topc(A_746) | ~v2_pre_topc(A_746) | v2_struct_0(A_746))), inference(resolution, [status(thm)], [c_863, c_818])).
% 3.90/1.62  tff(c_882, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_872])).
% 3.90/1.62  tff(c_890, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_682, c_108, c_657, c_882])).
% 3.90/1.62  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_890])).
% 3.90/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.62  
% 3.90/1.62  Inference rules
% 3.90/1.62  ----------------------
% 3.90/1.62  #Ref     : 0
% 3.90/1.62  #Sup     : 140
% 3.90/1.62  #Fact    : 0
% 3.90/1.62  #Define  : 0
% 3.90/1.62  #Split   : 18
% 3.90/1.62  #Chain   : 0
% 3.90/1.62  #Close   : 0
% 3.90/1.62  
% 3.90/1.62  Ordering : KBO
% 3.90/1.62  
% 3.90/1.62  Simplification rules
% 3.90/1.62  ----------------------
% 3.90/1.62  #Subsume      : 50
% 3.90/1.62  #Demod        : 181
% 3.90/1.62  #Tautology    : 34
% 3.90/1.62  #SimpNegUnit  : 27
% 3.90/1.62  #BackRed      : 2
% 3.90/1.62  
% 3.90/1.62  #Partial instantiations: 0
% 3.90/1.62  #Strategies tried      : 1
% 3.90/1.62  
% 3.90/1.62  Timing (in seconds)
% 3.90/1.62  ----------------------
% 3.90/1.62  Preprocessing        : 0.41
% 3.90/1.62  Parsing              : 0.20
% 3.90/1.62  CNF conversion       : 0.06
% 3.90/1.62  Main loop            : 0.43
% 3.90/1.62  Inferencing          : 0.15
% 3.90/1.62  Reduction            : 0.14
% 3.90/1.62  Demodulation         : 0.09
% 3.90/1.62  BG Simplification    : 0.02
% 3.90/1.62  Subsumption          : 0.09
% 3.90/1.62  Abstraction          : 0.01
% 3.90/1.62  MUC search           : 0.00
% 3.90/1.62  Cooper               : 0.00
% 3.90/1.62  Total                : 0.89
% 3.90/1.62  Index Insertion      : 0.00
% 3.90/1.62  Index Deletion       : 0.00
% 3.90/1.62  Index Matching       : 0.00
% 3.90/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
