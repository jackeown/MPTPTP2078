%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 27.73s
% Output     : CNFRefutation 27.92s
% Verified   : 
% Statistics : Number of formulae       :  200 (1068 expanded)
%              Number of leaves         :   50 ( 418 expanded)
%              Depth                    :   20
%              Number of atoms          :  643 (8497 expanded)
%              Number of equality atoms :   35 ( 390 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_386,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_229,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_215,axiom,(
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

tff(f_183,axiom,(
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

tff(f_316,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_156,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_269,axiom,(
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
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_84,plain,(
    m1_pre_topc('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_70,plain,(
    '#skF_11' = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_80,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_121,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_80])).

tff(c_78,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_102,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_100,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_96,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1055,plain,(
    ! [B_742,C_743,A_744] :
      ( m1_pre_topc(B_742,C_743)
      | ~ r1_tarski(u1_struct_0(B_742),u1_struct_0(C_743))
      | ~ m1_pre_topc(C_743,A_744)
      | ~ m1_pre_topc(B_742,A_744)
      | ~ l1_pre_topc(A_744)
      | ~ v2_pre_topc(A_744) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1060,plain,(
    ! [B_745,A_746] :
      ( m1_pre_topc(B_745,B_745)
      | ~ m1_pre_topc(B_745,A_746)
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746) ) ),
    inference(resolution,[status(thm)],[c_12,c_1055])).

tff(c_1066,plain,
    ( m1_pre_topc('#skF_7','#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_1060])).

tff(c_1075,plain,(
    m1_pre_topc('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_1066])).

tff(c_92,plain,(
    m1_pre_topc('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_239,plain,(
    ! [B_605,A_606] :
      ( v2_pre_topc(B_605)
      | ~ m1_pre_topc(B_605,A_606)
      | ~ l1_pre_topc(A_606)
      | ~ v2_pre_topc(A_606) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_245,plain,
    ( v2_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_239])).

tff(c_254,plain,(
    v2_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_245])).

tff(c_139,plain,(
    ! [B_583,A_584] :
      ( l1_pre_topc(B_583)
      | ~ m1_pre_topc(B_583,A_584)
      | ~ l1_pre_topc(A_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_145,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_139])).

tff(c_154,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_145])).

tff(c_1068,plain,
    ( m1_pre_topc('#skF_8','#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_1060])).

tff(c_1078,plain,(
    m1_pre_topc('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_1068])).

tff(c_1131,plain,(
    ! [B_751,C_752,A_753] :
      ( r1_tarski(u1_struct_0(B_751),u1_struct_0(C_752))
      | ~ m1_pre_topc(B_751,C_752)
      | ~ m1_pre_topc(C_752,A_753)
      | ~ m1_pre_topc(B_751,A_753)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1133,plain,(
    ! [B_751] :
      ( r1_tarski(u1_struct_0(B_751),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_751,'#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1078,c_1131])).

tff(c_1148,plain,(
    ! [B_751] :
      ( r1_tarski(u1_struct_0(B_751),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_751,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_154,c_1133])).

tff(c_242,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_239])).

tff(c_251,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_242])).

tff(c_142,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_139])).

tff(c_151,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_142])).

tff(c_1135,plain,(
    ! [B_751] :
      ( r1_tarski(u1_struct_0(B_751),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_751,'#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1075,c_1131])).

tff(c_1433,plain,(
    ! [B_762] :
      ( r1_tarski(u1_struct_0(B_762),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_762,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_151,c_1135])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k1_zfmisc_1(A_13),k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_202,plain,(
    ! [C_599,B_600,A_601] :
      ( r2_hidden(C_599,B_600)
      | ~ r2_hidden(C_599,A_601)
      | ~ r1_tarski(A_601,B_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_372,plain,(
    ! [C_627,B_628,A_629] :
      ( r2_hidden(C_627,B_628)
      | ~ r1_tarski(k1_zfmisc_1(A_629),B_628)
      | ~ r1_tarski(C_627,A_629) ) ),
    inference(resolution,[status(thm)],[c_16,c_202])).

tff(c_378,plain,(
    ! [C_627,B_14,A_13] :
      ( r2_hidden(C_627,k1_zfmisc_1(B_14))
      | ~ r1_tarski(C_627,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_2200,plain,(
    ! [B_811,B_812] :
      ( r2_hidden(u1_struct_0(B_811),k1_zfmisc_1(B_812))
      | ~ r1_tarski(u1_struct_0('#skF_7'),B_812)
      | ~ m1_pre_topc(B_811,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1433,c_378])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2245,plain,(
    ! [B_814,B_815] :
      ( r1_tarski(u1_struct_0(B_814),B_815)
      | ~ r1_tarski(u1_struct_0('#skF_7'),B_815)
      | ~ m1_pre_topc(B_814,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2200,c_14])).

tff(c_2251,plain,(
    ! [B_814] :
      ( r1_tarski(u1_struct_0(B_814),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_814,'#skF_7')
      | ~ m1_pre_topc('#skF_7','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1148,c_2245])).

tff(c_2260,plain,(
    ! [B_814] :
      ( r1_tarski(u1_struct_0(B_814),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_814,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2251])).

tff(c_134,plain,(
    ! [C_581,A_582] :
      ( r2_hidden(C_581,k1_zfmisc_1(A_582))
      | ~ r1_tarski(C_581,A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [C_581,A_582] :
      ( m1_subset_1(C_581,k1_zfmisc_1(A_582))
      | ~ r1_tarski(C_581,A_582) ) ),
    inference(resolution,[status(thm)],[c_134,c_28])).

tff(c_110,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_112,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12')
    | ~ r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_120,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12')
    | ~ r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_112])).

tff(c_212,plain,(
    ~ r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_108,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_106,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_90,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_88,plain,(
    v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_2984,plain,(
    ! [A_872,B_874,C_871,E_875,D_873] :
      ( k3_tmap_1(A_872,B_874,C_871,D_873,E_875) = k2_partfun1(u1_struct_0(C_871),u1_struct_0(B_874),E_875,u1_struct_0(D_873))
      | ~ m1_pre_topc(D_873,C_871)
      | ~ m1_subset_1(E_875,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_871),u1_struct_0(B_874))))
      | ~ v1_funct_2(E_875,u1_struct_0(C_871),u1_struct_0(B_874))
      | ~ v1_funct_1(E_875)
      | ~ m1_pre_topc(D_873,A_872)
      | ~ m1_pre_topc(C_871,A_872)
      | ~ l1_pre_topc(B_874)
      | ~ v2_pre_topc(B_874)
      | v2_struct_0(B_874)
      | ~ l1_pre_topc(A_872)
      | ~ v2_pre_topc(A_872)
      | v2_struct_0(A_872) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_3007,plain,(
    ! [A_872,D_873] :
      ( k3_tmap_1(A_872,'#skF_5','#skF_8',D_873,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_873))
      | ~ m1_pre_topc(D_873,'#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_873,A_872)
      | ~ m1_pre_topc('#skF_8',A_872)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_872)
      | ~ v2_pre_topc(A_872)
      | v2_struct_0(A_872) ) ),
    inference(resolution,[status(thm)],[c_86,c_2984])).

tff(c_3017,plain,(
    ! [A_872,D_873] :
      ( k3_tmap_1(A_872,'#skF_5','#skF_8',D_873,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_873))
      | ~ m1_pre_topc(D_873,'#skF_8')
      | ~ m1_pre_topc(D_873,A_872)
      | ~ m1_pre_topc('#skF_8',A_872)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_872)
      | ~ v2_pre_topc(A_872)
      | v2_struct_0(A_872) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_90,c_88,c_3007])).

tff(c_5553,plain,(
    ! [A_983,D_984] :
      ( k3_tmap_1(A_983,'#skF_5','#skF_8',D_984,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_984))
      | ~ m1_pre_topc(D_984,'#skF_8')
      | ~ m1_pre_topc(D_984,A_983)
      | ~ m1_pre_topc('#skF_8',A_983)
      | ~ l1_pre_topc(A_983)
      | ~ v2_pre_topc(A_983)
      | v2_struct_0(A_983) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_3017])).

tff(c_5563,plain,
    ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | ~ m1_pre_topc('#skF_7','#skF_8')
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_5553])).

tff(c_5584,plain,
    ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_92,c_84,c_5563])).

tff(c_5585,plain,(
    k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_5584])).

tff(c_2866,plain,(
    ! [A_852,B_853,C_854,D_855] :
      ( k2_partfun1(u1_struct_0(A_852),u1_struct_0(B_853),C_854,u1_struct_0(D_855)) = k2_tmap_1(A_852,B_853,C_854,D_855)
      | ~ m1_pre_topc(D_855,A_852)
      | ~ m1_subset_1(C_854,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_852),u1_struct_0(B_853))))
      | ~ v1_funct_2(C_854,u1_struct_0(A_852),u1_struct_0(B_853))
      | ~ v1_funct_1(C_854)
      | ~ l1_pre_topc(B_853)
      | ~ v2_pre_topc(B_853)
      | v2_struct_0(B_853)
      | ~ l1_pre_topc(A_852)
      | ~ v2_pre_topc(A_852)
      | v2_struct_0(A_852) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2889,plain,(
    ! [D_855] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_855)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_855)
      | ~ m1_pre_topc(D_855,'#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_86,c_2866])).

tff(c_2899,plain,(
    ! [D_855] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_855)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_855)
      | ~ m1_pre_topc(D_855,'#skF_8')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_154,c_108,c_106,c_90,c_88,c_2889])).

tff(c_2900,plain,(
    ! [D_855] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_855)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_855)
      | ~ m1_pre_topc(D_855,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_110,c_2899])).

tff(c_5741,plain,
    ( k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') = k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5585,c_2900])).

tff(c_5748,plain,(
    k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') = k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5741])).

tff(c_118,plain,
    ( r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_11')
    | r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_119,plain,
    ( r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12')
    | r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_118])).

tff(c_355,plain,(
    r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_119])).

tff(c_5753,plain,(
    r1_tmap_1('#skF_7','#skF_5',k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5748,c_355])).

tff(c_64,plain,(
    ! [B_261,E_317,C_293,A_197,D_309,G_323] :
      ( r1_tmap_1(B_261,A_197,C_293,G_323)
      | ~ r1_tmap_1(D_309,A_197,k2_tmap_1(B_261,A_197,C_293,D_309),G_323)
      | ~ m1_connsp_2(E_317,B_261,G_323)
      | ~ r1_tarski(E_317,u1_struct_0(D_309))
      | ~ m1_subset_1(G_323,u1_struct_0(D_309))
      | ~ m1_subset_1(G_323,u1_struct_0(B_261))
      | ~ m1_subset_1(E_317,k1_zfmisc_1(u1_struct_0(B_261)))
      | ~ m1_pre_topc(D_309,B_261)
      | v2_struct_0(D_309)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_261),u1_struct_0(A_197))))
      | ~ v1_funct_2(C_293,u1_struct_0(B_261),u1_struct_0(A_197))
      | ~ v1_funct_1(C_293)
      | ~ l1_pre_topc(B_261)
      | ~ v2_pre_topc(B_261)
      | v2_struct_0(B_261)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_316])).

tff(c_5759,plain,(
    ! [E_317] :
      ( r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12')
      | ~ m1_connsp_2(E_317,'#skF_8','#skF_12')
      | ~ r1_tarski(E_317,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_8'))
      | ~ m1_subset_1(E_317,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_pre_topc('#skF_7','#skF_8')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5753,c_64])).

tff(c_5762,plain,(
    ! [E_317] :
      ( r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12')
      | ~ m1_connsp_2(E_317,'#skF_8','#skF_12')
      | ~ r1_tarski(E_317,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_317,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_254,c_154,c_90,c_88,c_86,c_84,c_121,c_78,c_5759])).

tff(c_5781,plain,(
    ! [E_989] :
      ( ~ m1_connsp_2(E_989,'#skF_8','#skF_12')
      | ~ r1_tarski(E_989,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_989,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_94,c_98,c_212,c_5762])).

tff(c_5985,plain,(
    ! [C_995] :
      ( ~ m1_connsp_2(C_995,'#skF_8','#skF_12')
      | ~ r1_tarski(C_995,u1_struct_0('#skF_7'))
      | ~ r1_tarski(C_995,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_138,c_5781])).

tff(c_6045,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_8','#skF_12')
    | ~ r1_tarski(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_12,c_5985])).

tff(c_6046,plain,(
    ~ r1_tarski(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6045])).

tff(c_6052,plain,(
    ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_2260,c_6046])).

tff(c_6060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_6052])).

tff(c_6061,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_7'),'#skF_8','#skF_12') ),
    inference(splitRight,[status(thm)],[c_6045])).

tff(c_72,plain,(
    r1_tarski('#skF_10',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_6062,plain,(
    r1_tarski(u1_struct_0('#skF_7'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6045])).

tff(c_258,plain,(
    ! [A_607,C_608,B_609] :
      ( m1_subset_1(A_607,C_608)
      | ~ m1_subset_1(B_609,k1_zfmisc_1(C_608))
      | ~ r2_hidden(A_607,B_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_302,plain,(
    ! [A_614,A_615,C_616] :
      ( m1_subset_1(A_614,A_615)
      | ~ r2_hidden(A_614,C_616)
      | ~ r1_tarski(C_616,A_615) ) ),
    inference(resolution,[status(thm)],[c_138,c_258])).

tff(c_434,plain,(
    ! [C_641,A_642,A_643] :
      ( m1_subset_1(C_641,A_642)
      | ~ r1_tarski(k1_zfmisc_1(A_643),A_642)
      | ~ r1_tarski(C_641,A_643) ) ),
    inference(resolution,[status(thm)],[c_16,c_302])).

tff(c_440,plain,(
    ! [C_641,B_14,A_13] :
      ( m1_subset_1(C_641,k1_zfmisc_1(B_14))
      | ~ r1_tarski(C_641,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_434])).

tff(c_6190,plain,(
    ! [B_14] :
      ( m1_subset_1(u1_struct_0('#skF_7'),k1_zfmisc_1(B_14))
      | ~ r1_tarski(u1_struct_0('#skF_8'),B_14) ) ),
    inference(resolution,[status(thm)],[c_6062,c_440])).

tff(c_1163,plain,(
    ! [B_754] :
      ( r1_tarski(u1_struct_0(B_754),u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(B_754,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_154,c_1133])).

tff(c_380,plain,(
    ! [C_630,B_631,A_632] :
      ( r2_hidden(C_630,k1_zfmisc_1(B_631))
      | ~ r1_tarski(C_630,A_632)
      | ~ r1_tarski(A_632,B_631) ) ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_393,plain,(
    ! [B_633] :
      ( r2_hidden('#skF_10',k1_zfmisc_1(B_633))
      | ~ r1_tarski(u1_struct_0('#skF_7'),B_633) ) ),
    inference(resolution,[status(thm)],[c_72,c_380])).

tff(c_407,plain,(
    ! [B_633] :
      ( m1_subset_1('#skF_10',k1_zfmisc_1(B_633))
      | ~ r1_tarski(u1_struct_0('#skF_7'),B_633) ) ),
    inference(resolution,[status(thm)],[c_393,c_28])).

tff(c_1190,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_pre_topc('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1163,c_407])).

tff(c_1230,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1190])).

tff(c_74,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_122,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74])).

tff(c_2637,plain,(
    ! [C_835,A_836,B_837,D_838] :
      ( m1_connsp_2(C_835,A_836,B_837)
      | ~ r2_hidden(B_837,D_838)
      | ~ r1_tarski(D_838,C_835)
      | ~ v3_pre_topc(D_838,A_836)
      | ~ m1_subset_1(D_838,k1_zfmisc_1(u1_struct_0(A_836)))
      | ~ m1_subset_1(C_835,k1_zfmisc_1(u1_struct_0(A_836)))
      | ~ m1_subset_1(B_837,u1_struct_0(A_836))
      | ~ l1_pre_topc(A_836)
      | ~ v2_pre_topc(A_836)
      | v2_struct_0(A_836) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_6063,plain,(
    ! [C_996,A_997] :
      ( m1_connsp_2(C_996,A_997,'#skF_12')
      | ~ r1_tarski('#skF_10',C_996)
      | ~ v3_pre_topc('#skF_10',A_997)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0(A_997)))
      | ~ m1_subset_1(C_996,k1_zfmisc_1(u1_struct_0(A_997)))
      | ~ m1_subset_1('#skF_12',u1_struct_0(A_997))
      | ~ l1_pre_topc(A_997)
      | ~ v2_pre_topc(A_997)
      | v2_struct_0(A_997) ) ),
    inference(resolution,[status(thm)],[c_122,c_2637])).

tff(c_6073,plain,(
    ! [C_996] :
      ( m1_connsp_2(C_996,'#skF_8','#skF_12')
      | ~ r1_tarski('#skF_10',C_996)
      | ~ v3_pre_topc('#skF_10','#skF_8')
      | ~ m1_subset_1(C_996,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_8'))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1230,c_6063])).

tff(c_6099,plain,(
    ! [C_996] :
      ( m1_connsp_2(C_996,'#skF_8','#skF_12')
      | ~ r1_tarski('#skF_10',C_996)
      | ~ v3_pre_topc('#skF_10','#skF_8')
      | ~ m1_subset_1(C_996,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_154,c_121,c_6073])).

tff(c_6100,plain,(
    ! [C_996] :
      ( m1_connsp_2(C_996,'#skF_8','#skF_12')
      | ~ r1_tarski('#skF_10',C_996)
      | ~ v3_pre_topc('#skF_10','#skF_8')
      | ~ m1_subset_1(C_996,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6099])).

tff(c_6825,plain,(
    ~ v3_pre_topc('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6100])).

tff(c_406,plain,(
    ! [B_633] :
      ( r1_tarski('#skF_10',B_633)
      | ~ r1_tarski(u1_struct_0('#skF_7'),B_633) ) ),
    inference(resolution,[status(thm)],[c_393,c_14])).

tff(c_1194,plain,
    ( r1_tarski('#skF_10',u1_struct_0('#skF_8'))
    | ~ m1_pre_topc('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1163,c_406])).

tff(c_1233,plain,(
    r1_tarski('#skF_10',u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1194])).

tff(c_76,plain,(
    v3_pre_topc('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_386])).

tff(c_36,plain,(
    ! [C_32,A_26,B_30] :
      ( m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(B_30)))
      | ~ m1_pre_topc(B_30,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1381,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc('#skF_8',A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_1230,c_36])).

tff(c_1597,plain,(
    ! [D_768,C_769,A_770] :
      ( v3_pre_topc(D_768,C_769)
      | ~ m1_subset_1(D_768,k1_zfmisc_1(u1_struct_0(C_769)))
      | ~ v3_pre_topc(D_768,A_770)
      | ~ m1_pre_topc(C_769,A_770)
      | ~ m1_subset_1(D_768,k1_zfmisc_1(u1_struct_0(A_770)))
      | ~ l1_pre_topc(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_19996,plain,(
    ! [C_1361,C_1362,A_1363] :
      ( v3_pre_topc(C_1361,C_1362)
      | ~ v3_pre_topc(C_1361,A_1363)
      | ~ m1_pre_topc(C_1362,A_1363)
      | ~ m1_subset_1(C_1361,k1_zfmisc_1(u1_struct_0(A_1363)))
      | ~ l1_pre_topc(A_1363)
      | ~ r1_tarski(C_1361,u1_struct_0(C_1362)) ) ),
    inference(resolution,[status(thm)],[c_138,c_1597])).

tff(c_20008,plain,(
    ! [C_1361] :
      ( v3_pre_topc(C_1361,'#skF_8')
      | ~ v3_pre_topc(C_1361,'#skF_6')
      | ~ m1_subset_1(C_1361,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ r1_tarski(C_1361,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_92,c_19996])).

tff(c_57524,plain,(
    ! [C_2209] :
      ( v3_pre_topc(C_2209,'#skF_8')
      | ~ v3_pre_topc(C_2209,'#skF_6')
      | ~ m1_subset_1(C_2209,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski(C_2209,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_20008])).

tff(c_57653,plain,
    ( v3_pre_topc('#skF_10','#skF_8')
    | ~ v3_pre_topc('#skF_10','#skF_6')
    | ~ r1_tarski('#skF_10',u1_struct_0('#skF_8'))
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1381,c_57524])).

tff(c_57753,plain,(
    v3_pre_topc('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_92,c_1233,c_76,c_57653])).

tff(c_57755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6825,c_57753])).

tff(c_57758,plain,(
    ! [C_2210] :
      ( m1_connsp_2(C_2210,'#skF_8','#skF_12')
      | ~ r1_tarski('#skF_10',C_2210)
      | ~ m1_subset_1(C_2210,k1_zfmisc_1(u1_struct_0('#skF_8'))) ) ),
    inference(splitRight,[status(thm)],[c_6100])).

tff(c_57766,plain,
    ( m1_connsp_2(u1_struct_0('#skF_7'),'#skF_8','#skF_12')
    | ~ r1_tarski('#skF_10',u1_struct_0('#skF_7'))
    | ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6190,c_57758])).

tff(c_57825,plain,(
    m1_connsp_2(u1_struct_0('#skF_7'),'#skF_8','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72,c_57766])).

tff(c_57827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6061,c_57825])).

tff(c_57829,plain,(
    r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_57985,plain,(
    ! [B_2232,A_2233] :
      ( v2_pre_topc(B_2232)
      | ~ m1_pre_topc(B_2232,A_2233)
      | ~ l1_pre_topc(A_2233)
      | ~ v2_pre_topc(A_2233) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_57991,plain,
    ( v2_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_57985])).

tff(c_58000,plain,(
    v2_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_57991])).

tff(c_61602,plain,(
    ! [C_2526,A_2528,B_2527,F_2530,D_2529] :
      ( r1_tmap_1(D_2529,A_2528,k2_tmap_1(B_2527,A_2528,C_2526,D_2529),F_2530)
      | ~ r1_tmap_1(B_2527,A_2528,C_2526,F_2530)
      | ~ m1_subset_1(F_2530,u1_struct_0(D_2529))
      | ~ m1_subset_1(F_2530,u1_struct_0(B_2527))
      | ~ m1_pre_topc(D_2529,B_2527)
      | v2_struct_0(D_2529)
      | ~ m1_subset_1(C_2526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_2527),u1_struct_0(A_2528))))
      | ~ v1_funct_2(C_2526,u1_struct_0(B_2527),u1_struct_0(A_2528))
      | ~ v1_funct_1(C_2526)
      | ~ l1_pre_topc(B_2527)
      | ~ v2_pre_topc(B_2527)
      | v2_struct_0(B_2527)
      | ~ l1_pre_topc(A_2528)
      | ~ v2_pre_topc(A_2528)
      | v2_struct_0(A_2528) ) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_61625,plain,(
    ! [D_2529,F_2530] :
      ( r1_tmap_1(D_2529,'#skF_5',k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2529),F_2530)
      | ~ r1_tmap_1('#skF_8','#skF_5','#skF_9',F_2530)
      | ~ m1_subset_1(F_2530,u1_struct_0(D_2529))
      | ~ m1_subset_1(F_2530,u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(D_2529,'#skF_8')
      | v2_struct_0(D_2529)
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_61602])).

tff(c_61635,plain,(
    ! [D_2529,F_2530] :
      ( r1_tmap_1(D_2529,'#skF_5',k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2529),F_2530)
      | ~ r1_tmap_1('#skF_8','#skF_5','#skF_9',F_2530)
      | ~ m1_subset_1(F_2530,u1_struct_0(D_2529))
      | ~ m1_subset_1(F_2530,u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(D_2529,'#skF_8')
      | v2_struct_0(D_2529)
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_58000,c_154,c_90,c_88,c_61625])).

tff(c_61636,plain,(
    ! [D_2529,F_2530] :
      ( r1_tmap_1(D_2529,'#skF_5',k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2529),F_2530)
      | ~ r1_tmap_1('#skF_8','#skF_5','#skF_9',F_2530)
      | ~ m1_subset_1(F_2530,u1_struct_0(D_2529))
      | ~ m1_subset_1(F_2530,u1_struct_0('#skF_8'))
      | ~ m1_pre_topc(D_2529,'#skF_8')
      | v2_struct_0(D_2529) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_94,c_61635])).

tff(c_61141,plain,(
    ! [A_2513,E_2516,D_2514,C_2512,B_2515] :
      ( k3_tmap_1(A_2513,B_2515,C_2512,D_2514,E_2516) = k2_partfun1(u1_struct_0(C_2512),u1_struct_0(B_2515),E_2516,u1_struct_0(D_2514))
      | ~ m1_pre_topc(D_2514,C_2512)
      | ~ m1_subset_1(E_2516,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_2512),u1_struct_0(B_2515))))
      | ~ v1_funct_2(E_2516,u1_struct_0(C_2512),u1_struct_0(B_2515))
      | ~ v1_funct_1(E_2516)
      | ~ m1_pre_topc(D_2514,A_2513)
      | ~ m1_pre_topc(C_2512,A_2513)
      | ~ l1_pre_topc(B_2515)
      | ~ v2_pre_topc(B_2515)
      | v2_struct_0(B_2515)
      | ~ l1_pre_topc(A_2513)
      | ~ v2_pre_topc(A_2513)
      | v2_struct_0(A_2513) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_61164,plain,(
    ! [A_2513,D_2514] :
      ( k3_tmap_1(A_2513,'#skF_5','#skF_8',D_2514,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2514))
      | ~ m1_pre_topc(D_2514,'#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ m1_pre_topc(D_2514,A_2513)
      | ~ m1_pre_topc('#skF_8',A_2513)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_2513)
      | ~ v2_pre_topc(A_2513)
      | v2_struct_0(A_2513) ) ),
    inference(resolution,[status(thm)],[c_86,c_61141])).

tff(c_61174,plain,(
    ! [A_2513,D_2514] :
      ( k3_tmap_1(A_2513,'#skF_5','#skF_8',D_2514,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2514))
      | ~ m1_pre_topc(D_2514,'#skF_8')
      | ~ m1_pre_topc(D_2514,A_2513)
      | ~ m1_pre_topc('#skF_8',A_2513)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_2513)
      | ~ v2_pre_topc(A_2513)
      | v2_struct_0(A_2513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_90,c_88,c_61164])).

tff(c_64156,plain,(
    ! [A_2647,D_2648] :
      ( k3_tmap_1(A_2647,'#skF_5','#skF_8',D_2648,'#skF_9') = k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2648))
      | ~ m1_pre_topc(D_2648,'#skF_8')
      | ~ m1_pre_topc(D_2648,A_2647)
      | ~ m1_pre_topc('#skF_8',A_2647)
      | ~ l1_pre_topc(A_2647)
      | ~ v2_pre_topc(A_2647)
      | v2_struct_0(A_2647) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_61174])).

tff(c_64166,plain,
    ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | ~ m1_pre_topc('#skF_7','#skF_8')
    | ~ m1_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_64156])).

tff(c_64187,plain,
    ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_92,c_84,c_64166])).

tff(c_64188,plain,(
    k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0('#skF_7')) = k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_64187])).

tff(c_60900,plain,(
    ! [A_2495,B_2496,C_2497,D_2498] :
      ( k2_partfun1(u1_struct_0(A_2495),u1_struct_0(B_2496),C_2497,u1_struct_0(D_2498)) = k2_tmap_1(A_2495,B_2496,C_2497,D_2498)
      | ~ m1_pre_topc(D_2498,A_2495)
      | ~ m1_subset_1(C_2497,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2495),u1_struct_0(B_2496))))
      | ~ v1_funct_2(C_2497,u1_struct_0(A_2495),u1_struct_0(B_2496))
      | ~ v1_funct_1(C_2497)
      | ~ l1_pre_topc(B_2496)
      | ~ v2_pre_topc(B_2496)
      | v2_struct_0(B_2496)
      | ~ l1_pre_topc(A_2495)
      | ~ v2_pre_topc(A_2495)
      | v2_struct_0(A_2495) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60923,plain,(
    ! [D_2498] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2498)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2498)
      | ~ m1_pre_topc(D_2498,'#skF_8')
      | ~ v1_funct_2('#skF_9',u1_struct_0('#skF_8'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_9')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_86,c_60900])).

tff(c_60933,plain,(
    ! [D_2498] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2498)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2498)
      | ~ m1_pre_topc(D_2498,'#skF_8')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58000,c_154,c_108,c_106,c_90,c_88,c_60923])).

tff(c_60934,plain,(
    ! [D_2498] :
      ( k2_partfun1(u1_struct_0('#skF_8'),u1_struct_0('#skF_5'),'#skF_9',u1_struct_0(D_2498)) = k2_tmap_1('#skF_8','#skF_5','#skF_9',D_2498)
      | ~ m1_pre_topc(D_2498,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_110,c_60933])).

tff(c_64274,plain,
    ( k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') = k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_64188,c_60934])).

tff(c_64281,plain,(
    k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9') = k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64274])).

tff(c_57828,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_57830,plain,(
    r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_57955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57828,c_57830])).

tff(c_57957,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5',k3_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7','#skF_9'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_64286,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5',k2_tmap_1('#skF_8','#skF_5','#skF_9','#skF_7'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64281,c_57957])).

tff(c_64293,plain,
    ( ~ r1_tmap_1('#skF_8','#skF_5','#skF_9','#skF_12')
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_8'))
    | ~ m1_pre_topc('#skF_7','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_61636,c_64286])).

tff(c_64296,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_121,c_78,c_57829,c_64293])).

tff(c_64298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_64296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.73/18.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.73/18.10  
% 27.73/18.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.73/18.10  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_12
% 27.73/18.10  
% 27.73/18.10  %Foreground sorts:
% 27.73/18.10  
% 27.73/18.10  
% 27.73/18.10  %Background operators:
% 27.73/18.10  
% 27.73/18.10  
% 27.73/18.10  %Foreground operators:
% 27.73/18.10  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 27.73/18.10  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 27.73/18.10  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 27.73/18.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.73/18.10  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.73/18.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.73/18.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.73/18.10  tff('#skF_11', type, '#skF_11': $i).
% 27.73/18.10  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 27.73/18.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.73/18.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 27.73/18.10  tff('#skF_7', type, '#skF_7': $i).
% 27.73/18.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.73/18.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.73/18.10  tff('#skF_10', type, '#skF_10': $i).
% 27.73/18.10  tff('#skF_5', type, '#skF_5': $i).
% 27.73/18.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.73/18.10  tff('#skF_6', type, '#skF_6': $i).
% 27.73/18.10  tff('#skF_9', type, '#skF_9': $i).
% 27.73/18.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.73/18.10  tff('#skF_8', type, '#skF_8': $i).
% 27.73/18.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.73/18.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.73/18.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.73/18.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.73/18.10  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 27.73/18.10  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 27.73/18.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.73/18.10  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 27.73/18.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.73/18.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.73/18.10  tff('#skF_12', type, '#skF_12': $i).
% 27.73/18.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.73/18.10  
% 27.92/18.13  tff(f_386, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 27.92/18.13  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.92/18.13  tff(f_229, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 27.92/18.13  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 27.92/18.13  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 27.92/18.13  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 27.92/18.13  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 27.92/18.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 27.92/18.13  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 27.92/18.13  tff(f_215, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 27.92/18.13  tff(f_183, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 27.92/18.13  tff(f_316, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 27.92/18.13  tff(f_59, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 27.92/18.13  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 27.92/18.13  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 27.92/18.13  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 27.92/18.13  tff(f_269, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 27.92/18.13  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_84, plain, (m1_pre_topc('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_70, plain, ('#skF_11'='#skF_12'), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_80, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_121, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_80])).
% 27.92/18.13  tff(c_78, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_102, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_100, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.92/18.13  tff(c_1055, plain, (![B_742, C_743, A_744]: (m1_pre_topc(B_742, C_743) | ~r1_tarski(u1_struct_0(B_742), u1_struct_0(C_743)) | ~m1_pre_topc(C_743, A_744) | ~m1_pre_topc(B_742, A_744) | ~l1_pre_topc(A_744) | ~v2_pre_topc(A_744))), inference(cnfTransformation, [status(thm)], [f_229])).
% 27.92/18.13  tff(c_1060, plain, (![B_745, A_746]: (m1_pre_topc(B_745, B_745) | ~m1_pre_topc(B_745, A_746) | ~l1_pre_topc(A_746) | ~v2_pre_topc(A_746))), inference(resolution, [status(thm)], [c_12, c_1055])).
% 27.92/18.13  tff(c_1066, plain, (m1_pre_topc('#skF_7', '#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_96, c_1060])).
% 27.92/18.13  tff(c_1075, plain, (m1_pre_topc('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_1066])).
% 27.92/18.13  tff(c_92, plain, (m1_pre_topc('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_239, plain, (![B_605, A_606]: (v2_pre_topc(B_605) | ~m1_pre_topc(B_605, A_606) | ~l1_pre_topc(A_606) | ~v2_pre_topc(A_606))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.92/18.13  tff(c_245, plain, (v2_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_92, c_239])).
% 27.92/18.13  tff(c_254, plain, (v2_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_245])).
% 27.92/18.13  tff(c_139, plain, (![B_583, A_584]: (l1_pre_topc(B_583) | ~m1_pre_topc(B_583, A_584) | ~l1_pre_topc(A_584))), inference(cnfTransformation, [status(thm)], [f_75])).
% 27.92/18.13  tff(c_145, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_92, c_139])).
% 27.92/18.13  tff(c_154, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_145])).
% 27.92/18.13  tff(c_1068, plain, (m1_pre_topc('#skF_8', '#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_92, c_1060])).
% 27.92/18.13  tff(c_1078, plain, (m1_pre_topc('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_1068])).
% 27.92/18.13  tff(c_1131, plain, (![B_751, C_752, A_753]: (r1_tarski(u1_struct_0(B_751), u1_struct_0(C_752)) | ~m1_pre_topc(B_751, C_752) | ~m1_pre_topc(C_752, A_753) | ~m1_pre_topc(B_751, A_753) | ~l1_pre_topc(A_753) | ~v2_pre_topc(A_753))), inference(cnfTransformation, [status(thm)], [f_229])).
% 27.92/18.13  tff(c_1133, plain, (![B_751]: (r1_tarski(u1_struct_0(B_751), u1_struct_0('#skF_8')) | ~m1_pre_topc(B_751, '#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_1078, c_1131])).
% 27.92/18.13  tff(c_1148, plain, (![B_751]: (r1_tarski(u1_struct_0(B_751), u1_struct_0('#skF_8')) | ~m1_pre_topc(B_751, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_154, c_1133])).
% 27.92/18.13  tff(c_242, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_96, c_239])).
% 27.92/18.13  tff(c_251, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_242])).
% 27.92/18.13  tff(c_142, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_96, c_139])).
% 27.92/18.13  tff(c_151, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_142])).
% 27.92/18.13  tff(c_1135, plain, (![B_751]: (r1_tarski(u1_struct_0(B_751), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_751, '#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_1075, c_1131])).
% 27.92/18.13  tff(c_1433, plain, (![B_762]: (r1_tarski(u1_struct_0(B_762), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_762, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_151, c_1135])).
% 27.92/18.13  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(k1_zfmisc_1(A_13), k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 27.92/18.13  tff(c_16, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.92/18.13  tff(c_202, plain, (![C_599, B_600, A_601]: (r2_hidden(C_599, B_600) | ~r2_hidden(C_599, A_601) | ~r1_tarski(A_601, B_600))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.92/18.13  tff(c_372, plain, (![C_627, B_628, A_629]: (r2_hidden(C_627, B_628) | ~r1_tarski(k1_zfmisc_1(A_629), B_628) | ~r1_tarski(C_627, A_629))), inference(resolution, [status(thm)], [c_16, c_202])).
% 27.92/18.13  tff(c_378, plain, (![C_627, B_14, A_13]: (r2_hidden(C_627, k1_zfmisc_1(B_14)) | ~r1_tarski(C_627, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_26, c_372])).
% 27.92/18.13  tff(c_2200, plain, (![B_811, B_812]: (r2_hidden(u1_struct_0(B_811), k1_zfmisc_1(B_812)) | ~r1_tarski(u1_struct_0('#skF_7'), B_812) | ~m1_pre_topc(B_811, '#skF_7'))), inference(resolution, [status(thm)], [c_1433, c_378])).
% 27.92/18.13  tff(c_14, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.92/18.13  tff(c_2245, plain, (![B_814, B_815]: (r1_tarski(u1_struct_0(B_814), B_815) | ~r1_tarski(u1_struct_0('#skF_7'), B_815) | ~m1_pre_topc(B_814, '#skF_7'))), inference(resolution, [status(thm)], [c_2200, c_14])).
% 27.92/18.13  tff(c_2251, plain, (![B_814]: (r1_tarski(u1_struct_0(B_814), u1_struct_0('#skF_8')) | ~m1_pre_topc(B_814, '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_1148, c_2245])).
% 27.92/18.13  tff(c_2260, plain, (![B_814]: (r1_tarski(u1_struct_0(B_814), u1_struct_0('#skF_8')) | ~m1_pre_topc(B_814, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2251])).
% 27.92/18.13  tff(c_134, plain, (![C_581, A_582]: (r2_hidden(C_581, k1_zfmisc_1(A_582)) | ~r1_tarski(C_581, A_582))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.92/18.13  tff(c_28, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.92/18.13  tff(c_138, plain, (![C_581, A_582]: (m1_subset_1(C_581, k1_zfmisc_1(A_582)) | ~r1_tarski(C_581, A_582))), inference(resolution, [status(thm)], [c_134, c_28])).
% 27.92/18.13  tff(c_110, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_94, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_112, plain, (~r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12') | ~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_120, plain, (~r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12') | ~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_112])).
% 27.92/18.13  tff(c_212, plain, (~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12')), inference(splitLeft, [status(thm)], [c_120])).
% 27.92/18.13  tff(c_108, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_106, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_90, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_88, plain, (v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_86, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_104, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_2984, plain, (![A_872, B_874, C_871, E_875, D_873]: (k3_tmap_1(A_872, B_874, C_871, D_873, E_875)=k2_partfun1(u1_struct_0(C_871), u1_struct_0(B_874), E_875, u1_struct_0(D_873)) | ~m1_pre_topc(D_873, C_871) | ~m1_subset_1(E_875, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_871), u1_struct_0(B_874)))) | ~v1_funct_2(E_875, u1_struct_0(C_871), u1_struct_0(B_874)) | ~v1_funct_1(E_875) | ~m1_pre_topc(D_873, A_872) | ~m1_pre_topc(C_871, A_872) | ~l1_pre_topc(B_874) | ~v2_pre_topc(B_874) | v2_struct_0(B_874) | ~l1_pre_topc(A_872) | ~v2_pre_topc(A_872) | v2_struct_0(A_872))), inference(cnfTransformation, [status(thm)], [f_215])).
% 27.92/18.13  tff(c_3007, plain, (![A_872, D_873]: (k3_tmap_1(A_872, '#skF_5', '#skF_8', D_873, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_873)) | ~m1_pre_topc(D_873, '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_873, A_872) | ~m1_pre_topc('#skF_8', A_872) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc(A_872) | ~v2_pre_topc(A_872) | v2_struct_0(A_872))), inference(resolution, [status(thm)], [c_86, c_2984])).
% 27.92/18.13  tff(c_3017, plain, (![A_872, D_873]: (k3_tmap_1(A_872, '#skF_5', '#skF_8', D_873, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_873)) | ~m1_pre_topc(D_873, '#skF_8') | ~m1_pre_topc(D_873, A_872) | ~m1_pre_topc('#skF_8', A_872) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_872) | ~v2_pre_topc(A_872) | v2_struct_0(A_872))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_90, c_88, c_3007])).
% 27.92/18.13  tff(c_5553, plain, (![A_983, D_984]: (k3_tmap_1(A_983, '#skF_5', '#skF_8', D_984, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_984)) | ~m1_pre_topc(D_984, '#skF_8') | ~m1_pre_topc(D_984, A_983) | ~m1_pre_topc('#skF_8', A_983) | ~l1_pre_topc(A_983) | ~v2_pre_topc(A_983) | v2_struct_0(A_983))), inference(negUnitSimplification, [status(thm)], [c_110, c_3017])).
% 27.92/18.13  tff(c_5563, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | ~m1_pre_topc('#skF_7', '#skF_8') | ~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_96, c_5553])).
% 27.92/18.13  tff(c_5584, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_92, c_84, c_5563])).
% 27.92/18.13  tff(c_5585, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_104, c_5584])).
% 27.92/18.13  tff(c_2866, plain, (![A_852, B_853, C_854, D_855]: (k2_partfun1(u1_struct_0(A_852), u1_struct_0(B_853), C_854, u1_struct_0(D_855))=k2_tmap_1(A_852, B_853, C_854, D_855) | ~m1_pre_topc(D_855, A_852) | ~m1_subset_1(C_854, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_852), u1_struct_0(B_853)))) | ~v1_funct_2(C_854, u1_struct_0(A_852), u1_struct_0(B_853)) | ~v1_funct_1(C_854) | ~l1_pre_topc(B_853) | ~v2_pre_topc(B_853) | v2_struct_0(B_853) | ~l1_pre_topc(A_852) | ~v2_pre_topc(A_852) | v2_struct_0(A_852))), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.92/18.13  tff(c_2889, plain, (![D_855]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_855))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_855) | ~m1_pre_topc(D_855, '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_86, c_2866])).
% 27.92/18.13  tff(c_2899, plain, (![D_855]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_855))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_855) | ~m1_pre_topc(D_855, '#skF_8') | v2_struct_0('#skF_5') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_154, c_108, c_106, c_90, c_88, c_2889])).
% 27.92/18.13  tff(c_2900, plain, (![D_855]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_855))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_855) | ~m1_pre_topc(D_855, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_94, c_110, c_2899])).
% 27.92/18.13  tff(c_5741, plain, (k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5585, c_2900])).
% 27.92/18.13  tff(c_5748, plain, (k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5741])).
% 27.92/18.13  tff(c_118, plain, (r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_11') | r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_119, plain, (r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12') | r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_118])).
% 27.92/18.13  tff(c_355, plain, (r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_212, c_119])).
% 27.92/18.13  tff(c_5753, plain, (r1_tmap_1('#skF_7', '#skF_5', k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5748, c_355])).
% 27.92/18.13  tff(c_64, plain, (![B_261, E_317, C_293, A_197, D_309, G_323]: (r1_tmap_1(B_261, A_197, C_293, G_323) | ~r1_tmap_1(D_309, A_197, k2_tmap_1(B_261, A_197, C_293, D_309), G_323) | ~m1_connsp_2(E_317, B_261, G_323) | ~r1_tarski(E_317, u1_struct_0(D_309)) | ~m1_subset_1(G_323, u1_struct_0(D_309)) | ~m1_subset_1(G_323, u1_struct_0(B_261)) | ~m1_subset_1(E_317, k1_zfmisc_1(u1_struct_0(B_261))) | ~m1_pre_topc(D_309, B_261) | v2_struct_0(D_309) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_261), u1_struct_0(A_197)))) | ~v1_funct_2(C_293, u1_struct_0(B_261), u1_struct_0(A_197)) | ~v1_funct_1(C_293) | ~l1_pre_topc(B_261) | ~v2_pre_topc(B_261) | v2_struct_0(B_261) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_316])).
% 27.92/18.13  tff(c_5759, plain, (![E_317]: (r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12') | ~m1_connsp_2(E_317, '#skF_8', '#skF_12') | ~r1_tarski(E_317, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~m1_subset_1(E_317, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_pre_topc('#skF_7', '#skF_8') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_5753, c_64])).
% 27.92/18.13  tff(c_5762, plain, (![E_317]: (r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12') | ~m1_connsp_2(E_317, '#skF_8', '#skF_12') | ~r1_tarski(E_317, u1_struct_0('#skF_7')) | ~m1_subset_1(E_317, k1_zfmisc_1(u1_struct_0('#skF_8'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_8') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_254, c_154, c_90, c_88, c_86, c_84, c_121, c_78, c_5759])).
% 27.92/18.13  tff(c_5781, plain, (![E_989]: (~m1_connsp_2(E_989, '#skF_8', '#skF_12') | ~r1_tarski(E_989, u1_struct_0('#skF_7')) | ~m1_subset_1(E_989, k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_110, c_94, c_98, c_212, c_5762])).
% 27.92/18.13  tff(c_5985, plain, (![C_995]: (~m1_connsp_2(C_995, '#skF_8', '#skF_12') | ~r1_tarski(C_995, u1_struct_0('#skF_7')) | ~r1_tarski(C_995, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_138, c_5781])).
% 27.92/18.13  tff(c_6045, plain, (~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_8', '#skF_12') | ~r1_tarski(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_5985])).
% 27.92/18.13  tff(c_6046, plain, (~r1_tarski(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_6045])).
% 27.92/18.13  tff(c_6052, plain, (~m1_pre_topc('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_2260, c_6046])).
% 27.92/18.13  tff(c_6060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1075, c_6052])).
% 27.92/18.13  tff(c_6061, plain, (~m1_connsp_2(u1_struct_0('#skF_7'), '#skF_8', '#skF_12')), inference(splitRight, [status(thm)], [c_6045])).
% 27.92/18.13  tff(c_72, plain, (r1_tarski('#skF_10', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_6062, plain, (r1_tarski(u1_struct_0('#skF_7'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_6045])).
% 27.92/18.13  tff(c_258, plain, (![A_607, C_608, B_609]: (m1_subset_1(A_607, C_608) | ~m1_subset_1(B_609, k1_zfmisc_1(C_608)) | ~r2_hidden(A_607, B_609))), inference(cnfTransformation, [status(thm)], [f_59])).
% 27.92/18.13  tff(c_302, plain, (![A_614, A_615, C_616]: (m1_subset_1(A_614, A_615) | ~r2_hidden(A_614, C_616) | ~r1_tarski(C_616, A_615))), inference(resolution, [status(thm)], [c_138, c_258])).
% 27.92/18.13  tff(c_434, plain, (![C_641, A_642, A_643]: (m1_subset_1(C_641, A_642) | ~r1_tarski(k1_zfmisc_1(A_643), A_642) | ~r1_tarski(C_641, A_643))), inference(resolution, [status(thm)], [c_16, c_302])).
% 27.92/18.13  tff(c_440, plain, (![C_641, B_14, A_13]: (m1_subset_1(C_641, k1_zfmisc_1(B_14)) | ~r1_tarski(C_641, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_26, c_434])).
% 27.92/18.13  tff(c_6190, plain, (![B_14]: (m1_subset_1(u1_struct_0('#skF_7'), k1_zfmisc_1(B_14)) | ~r1_tarski(u1_struct_0('#skF_8'), B_14))), inference(resolution, [status(thm)], [c_6062, c_440])).
% 27.92/18.13  tff(c_1163, plain, (![B_754]: (r1_tarski(u1_struct_0(B_754), u1_struct_0('#skF_8')) | ~m1_pre_topc(B_754, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_154, c_1133])).
% 27.92/18.13  tff(c_380, plain, (![C_630, B_631, A_632]: (r2_hidden(C_630, k1_zfmisc_1(B_631)) | ~r1_tarski(C_630, A_632) | ~r1_tarski(A_632, B_631))), inference(resolution, [status(thm)], [c_26, c_372])).
% 27.92/18.13  tff(c_393, plain, (![B_633]: (r2_hidden('#skF_10', k1_zfmisc_1(B_633)) | ~r1_tarski(u1_struct_0('#skF_7'), B_633))), inference(resolution, [status(thm)], [c_72, c_380])).
% 27.92/18.13  tff(c_407, plain, (![B_633]: (m1_subset_1('#skF_10', k1_zfmisc_1(B_633)) | ~r1_tarski(u1_struct_0('#skF_7'), B_633))), inference(resolution, [status(thm)], [c_393, c_28])).
% 27.92/18.13  tff(c_1190, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_pre_topc('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_1163, c_407])).
% 27.92/18.13  tff(c_1230, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1190])).
% 27.92/18.13  tff(c_74, plain, (r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_122, plain, (r2_hidden('#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74])).
% 27.92/18.13  tff(c_2637, plain, (![C_835, A_836, B_837, D_838]: (m1_connsp_2(C_835, A_836, B_837) | ~r2_hidden(B_837, D_838) | ~r1_tarski(D_838, C_835) | ~v3_pre_topc(D_838, A_836) | ~m1_subset_1(D_838, k1_zfmisc_1(u1_struct_0(A_836))) | ~m1_subset_1(C_835, k1_zfmisc_1(u1_struct_0(A_836))) | ~m1_subset_1(B_837, u1_struct_0(A_836)) | ~l1_pre_topc(A_836) | ~v2_pre_topc(A_836) | v2_struct_0(A_836))), inference(cnfTransformation, [status(thm)], [f_156])).
% 27.92/18.13  tff(c_6063, plain, (![C_996, A_997]: (m1_connsp_2(C_996, A_997, '#skF_12') | ~r1_tarski('#skF_10', C_996) | ~v3_pre_topc('#skF_10', A_997) | ~m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0(A_997))) | ~m1_subset_1(C_996, k1_zfmisc_1(u1_struct_0(A_997))) | ~m1_subset_1('#skF_12', u1_struct_0(A_997)) | ~l1_pre_topc(A_997) | ~v2_pre_topc(A_997) | v2_struct_0(A_997))), inference(resolution, [status(thm)], [c_122, c_2637])).
% 27.92/18.13  tff(c_6073, plain, (![C_996]: (m1_connsp_2(C_996, '#skF_8', '#skF_12') | ~r1_tarski('#skF_10', C_996) | ~v3_pre_topc('#skF_10', '#skF_8') | ~m1_subset_1(C_996, k1_zfmisc_1(u1_struct_0('#skF_8'))) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1230, c_6063])).
% 27.92/18.13  tff(c_6099, plain, (![C_996]: (m1_connsp_2(C_996, '#skF_8', '#skF_12') | ~r1_tarski('#skF_10', C_996) | ~v3_pre_topc('#skF_10', '#skF_8') | ~m1_subset_1(C_996, k1_zfmisc_1(u1_struct_0('#skF_8'))) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_154, c_121, c_6073])).
% 27.92/18.13  tff(c_6100, plain, (![C_996]: (m1_connsp_2(C_996, '#skF_8', '#skF_12') | ~r1_tarski('#skF_10', C_996) | ~v3_pre_topc('#skF_10', '#skF_8') | ~m1_subset_1(C_996, k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(negUnitSimplification, [status(thm)], [c_94, c_6099])).
% 27.92/18.13  tff(c_6825, plain, (~v3_pre_topc('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_6100])).
% 27.92/18.13  tff(c_406, plain, (![B_633]: (r1_tarski('#skF_10', B_633) | ~r1_tarski(u1_struct_0('#skF_7'), B_633))), inference(resolution, [status(thm)], [c_393, c_14])).
% 27.92/18.13  tff(c_1194, plain, (r1_tarski('#skF_10', u1_struct_0('#skF_8')) | ~m1_pre_topc('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_1163, c_406])).
% 27.92/18.13  tff(c_1233, plain, (r1_tarski('#skF_10', u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1194])).
% 27.92/18.13  tff(c_76, plain, (v3_pre_topc('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_386])).
% 27.92/18.13  tff(c_36, plain, (![C_32, A_26, B_30]: (m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(B_30))) | ~m1_pre_topc(B_30, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 27.92/18.13  tff(c_1381, plain, (![A_26]: (m1_subset_1('#skF_10', k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc('#skF_8', A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_1230, c_36])).
% 27.92/18.13  tff(c_1597, plain, (![D_768, C_769, A_770]: (v3_pre_topc(D_768, C_769) | ~m1_subset_1(D_768, k1_zfmisc_1(u1_struct_0(C_769))) | ~v3_pre_topc(D_768, A_770) | ~m1_pre_topc(C_769, A_770) | ~m1_subset_1(D_768, k1_zfmisc_1(u1_struct_0(A_770))) | ~l1_pre_topc(A_770))), inference(cnfTransformation, [status(thm)], [f_118])).
% 27.92/18.13  tff(c_19996, plain, (![C_1361, C_1362, A_1363]: (v3_pre_topc(C_1361, C_1362) | ~v3_pre_topc(C_1361, A_1363) | ~m1_pre_topc(C_1362, A_1363) | ~m1_subset_1(C_1361, k1_zfmisc_1(u1_struct_0(A_1363))) | ~l1_pre_topc(A_1363) | ~r1_tarski(C_1361, u1_struct_0(C_1362)))), inference(resolution, [status(thm)], [c_138, c_1597])).
% 27.92/18.13  tff(c_20008, plain, (![C_1361]: (v3_pre_topc(C_1361, '#skF_8') | ~v3_pre_topc(C_1361, '#skF_6') | ~m1_subset_1(C_1361, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~r1_tarski(C_1361, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_92, c_19996])).
% 27.92/18.13  tff(c_57524, plain, (![C_2209]: (v3_pre_topc(C_2209, '#skF_8') | ~v3_pre_topc(C_2209, '#skF_6') | ~m1_subset_1(C_2209, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski(C_2209, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_20008])).
% 27.92/18.13  tff(c_57653, plain, (v3_pre_topc('#skF_10', '#skF_8') | ~v3_pre_topc('#skF_10', '#skF_6') | ~r1_tarski('#skF_10', u1_struct_0('#skF_8')) | ~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1381, c_57524])).
% 27.92/18.13  tff(c_57753, plain, (v3_pre_topc('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_92, c_1233, c_76, c_57653])).
% 27.92/18.13  tff(c_57755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6825, c_57753])).
% 27.92/18.13  tff(c_57758, plain, (![C_2210]: (m1_connsp_2(C_2210, '#skF_8', '#skF_12') | ~r1_tarski('#skF_10', C_2210) | ~m1_subset_1(C_2210, k1_zfmisc_1(u1_struct_0('#skF_8'))))), inference(splitRight, [status(thm)], [c_6100])).
% 27.92/18.13  tff(c_57766, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_8', '#skF_12') | ~r1_tarski('#skF_10', u1_struct_0('#skF_7')) | ~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_6190, c_57758])).
% 27.92/18.13  tff(c_57825, plain, (m1_connsp_2(u1_struct_0('#skF_7'), '#skF_8', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_72, c_57766])).
% 27.92/18.13  tff(c_57827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6061, c_57825])).
% 27.92/18.13  tff(c_57829, plain, (r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12')), inference(splitRight, [status(thm)], [c_120])).
% 27.92/18.13  tff(c_57985, plain, (![B_2232, A_2233]: (v2_pre_topc(B_2232) | ~m1_pre_topc(B_2232, A_2233) | ~l1_pre_topc(A_2233) | ~v2_pre_topc(A_2233))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.92/18.13  tff(c_57991, plain, (v2_pre_topc('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_92, c_57985])).
% 27.92/18.13  tff(c_58000, plain, (v2_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_57991])).
% 27.92/18.13  tff(c_61602, plain, (![C_2526, A_2528, B_2527, F_2530, D_2529]: (r1_tmap_1(D_2529, A_2528, k2_tmap_1(B_2527, A_2528, C_2526, D_2529), F_2530) | ~r1_tmap_1(B_2527, A_2528, C_2526, F_2530) | ~m1_subset_1(F_2530, u1_struct_0(D_2529)) | ~m1_subset_1(F_2530, u1_struct_0(B_2527)) | ~m1_pre_topc(D_2529, B_2527) | v2_struct_0(D_2529) | ~m1_subset_1(C_2526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_2527), u1_struct_0(A_2528)))) | ~v1_funct_2(C_2526, u1_struct_0(B_2527), u1_struct_0(A_2528)) | ~v1_funct_1(C_2526) | ~l1_pre_topc(B_2527) | ~v2_pre_topc(B_2527) | v2_struct_0(B_2527) | ~l1_pre_topc(A_2528) | ~v2_pre_topc(A_2528) | v2_struct_0(A_2528))), inference(cnfTransformation, [status(thm)], [f_269])).
% 27.92/18.13  tff(c_61625, plain, (![D_2529, F_2530]: (r1_tmap_1(D_2529, '#skF_5', k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2529), F_2530) | ~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', F_2530) | ~m1_subset_1(F_2530, u1_struct_0(D_2529)) | ~m1_subset_1(F_2530, u1_struct_0('#skF_8')) | ~m1_pre_topc(D_2529, '#skF_8') | v2_struct_0(D_2529) | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_86, c_61602])).
% 27.92/18.13  tff(c_61635, plain, (![D_2529, F_2530]: (r1_tmap_1(D_2529, '#skF_5', k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2529), F_2530) | ~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', F_2530) | ~m1_subset_1(F_2530, u1_struct_0(D_2529)) | ~m1_subset_1(F_2530, u1_struct_0('#skF_8')) | ~m1_pre_topc(D_2529, '#skF_8') | v2_struct_0(D_2529) | v2_struct_0('#skF_8') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_58000, c_154, c_90, c_88, c_61625])).
% 27.92/18.13  tff(c_61636, plain, (![D_2529, F_2530]: (r1_tmap_1(D_2529, '#skF_5', k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2529), F_2530) | ~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', F_2530) | ~m1_subset_1(F_2530, u1_struct_0(D_2529)) | ~m1_subset_1(F_2530, u1_struct_0('#skF_8')) | ~m1_pre_topc(D_2529, '#skF_8') | v2_struct_0(D_2529))), inference(negUnitSimplification, [status(thm)], [c_110, c_94, c_61635])).
% 27.92/18.13  tff(c_61141, plain, (![A_2513, E_2516, D_2514, C_2512, B_2515]: (k3_tmap_1(A_2513, B_2515, C_2512, D_2514, E_2516)=k2_partfun1(u1_struct_0(C_2512), u1_struct_0(B_2515), E_2516, u1_struct_0(D_2514)) | ~m1_pre_topc(D_2514, C_2512) | ~m1_subset_1(E_2516, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_2512), u1_struct_0(B_2515)))) | ~v1_funct_2(E_2516, u1_struct_0(C_2512), u1_struct_0(B_2515)) | ~v1_funct_1(E_2516) | ~m1_pre_topc(D_2514, A_2513) | ~m1_pre_topc(C_2512, A_2513) | ~l1_pre_topc(B_2515) | ~v2_pre_topc(B_2515) | v2_struct_0(B_2515) | ~l1_pre_topc(A_2513) | ~v2_pre_topc(A_2513) | v2_struct_0(A_2513))), inference(cnfTransformation, [status(thm)], [f_215])).
% 27.92/18.13  tff(c_61164, plain, (![A_2513, D_2514]: (k3_tmap_1(A_2513, '#skF_5', '#skF_8', D_2514, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2514)) | ~m1_pre_topc(D_2514, '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~m1_pre_topc(D_2514, A_2513) | ~m1_pre_topc('#skF_8', A_2513) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc(A_2513) | ~v2_pre_topc(A_2513) | v2_struct_0(A_2513))), inference(resolution, [status(thm)], [c_86, c_61141])).
% 27.92/18.13  tff(c_61174, plain, (![A_2513, D_2514]: (k3_tmap_1(A_2513, '#skF_5', '#skF_8', D_2514, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2514)) | ~m1_pre_topc(D_2514, '#skF_8') | ~m1_pre_topc(D_2514, A_2513) | ~m1_pre_topc('#skF_8', A_2513) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_2513) | ~v2_pre_topc(A_2513) | v2_struct_0(A_2513))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_90, c_88, c_61164])).
% 27.92/18.13  tff(c_64156, plain, (![A_2647, D_2648]: (k3_tmap_1(A_2647, '#skF_5', '#skF_8', D_2648, '#skF_9')=k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2648)) | ~m1_pre_topc(D_2648, '#skF_8') | ~m1_pre_topc(D_2648, A_2647) | ~m1_pre_topc('#skF_8', A_2647) | ~l1_pre_topc(A_2647) | ~v2_pre_topc(A_2647) | v2_struct_0(A_2647))), inference(negUnitSimplification, [status(thm)], [c_110, c_61174])).
% 27.92/18.13  tff(c_64166, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | ~m1_pre_topc('#skF_7', '#skF_8') | ~m1_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_96, c_64156])).
% 27.92/18.13  tff(c_64187, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_92, c_84, c_64166])).
% 27.92/18.13  tff(c_64188, plain, (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0('#skF_7'))=k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_104, c_64187])).
% 27.92/18.13  tff(c_60900, plain, (![A_2495, B_2496, C_2497, D_2498]: (k2_partfun1(u1_struct_0(A_2495), u1_struct_0(B_2496), C_2497, u1_struct_0(D_2498))=k2_tmap_1(A_2495, B_2496, C_2497, D_2498) | ~m1_pre_topc(D_2498, A_2495) | ~m1_subset_1(C_2497, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2495), u1_struct_0(B_2496)))) | ~v1_funct_2(C_2497, u1_struct_0(A_2495), u1_struct_0(B_2496)) | ~v1_funct_1(C_2497) | ~l1_pre_topc(B_2496) | ~v2_pre_topc(B_2496) | v2_struct_0(B_2496) | ~l1_pre_topc(A_2495) | ~v2_pre_topc(A_2495) | v2_struct_0(A_2495))), inference(cnfTransformation, [status(thm)], [f_183])).
% 27.92/18.13  tff(c_60923, plain, (![D_2498]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2498))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2498) | ~m1_pre_topc(D_2498, '#skF_8') | ~v1_funct_2('#skF_9', u1_struct_0('#skF_8'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_9') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_86, c_60900])).
% 27.92/18.13  tff(c_60933, plain, (![D_2498]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2498))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2498) | ~m1_pre_topc(D_2498, '#skF_8') | v2_struct_0('#skF_5') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_58000, c_154, c_108, c_106, c_90, c_88, c_60923])).
% 27.92/18.13  tff(c_60934, plain, (![D_2498]: (k2_partfun1(u1_struct_0('#skF_8'), u1_struct_0('#skF_5'), '#skF_9', u1_struct_0(D_2498))=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', D_2498) | ~m1_pre_topc(D_2498, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_94, c_110, c_60933])).
% 27.92/18.13  tff(c_64274, plain, (k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_64188, c_60934])).
% 27.92/18.13  tff(c_64281, plain, (k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9')=k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64274])).
% 27.92/18.13  tff(c_57828, plain, (~r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(splitRight, [status(thm)], [c_120])).
% 27.92/18.13  tff(c_57830, plain, (r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(splitLeft, [status(thm)], [c_119])).
% 27.92/18.13  tff(c_57955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57828, c_57830])).
% 27.92/18.13  tff(c_57957, plain, (~r1_tmap_1('#skF_7', '#skF_5', k3_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7', '#skF_9'), '#skF_12')), inference(splitRight, [status(thm)], [c_119])).
% 27.92/18.13  tff(c_64286, plain, (~r1_tmap_1('#skF_7', '#skF_5', k2_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_7'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_64281, c_57957])).
% 27.92/18.13  tff(c_64293, plain, (~r1_tmap_1('#skF_8', '#skF_5', '#skF_9', '#skF_12') | ~m1_subset_1('#skF_12', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_8')) | ~m1_pre_topc('#skF_7', '#skF_8') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_61636, c_64286])).
% 27.92/18.13  tff(c_64296, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_121, c_78, c_57829, c_64293])).
% 27.92/18.13  tff(c_64298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_64296])).
% 27.92/18.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.92/18.13  
% 27.92/18.13  Inference rules
% 27.92/18.13  ----------------------
% 27.92/18.13  #Ref     : 0
% 27.92/18.13  #Sup     : 16719
% 27.92/18.13  #Fact    : 0
% 27.92/18.13  #Define  : 0
% 27.92/18.13  #Split   : 85
% 27.92/18.13  #Chain   : 0
% 27.92/18.13  #Close   : 0
% 27.92/18.13  
% 27.92/18.13  Ordering : KBO
% 27.92/18.13  
% 27.92/18.13  Simplification rules
% 27.92/18.13  ----------------------
% 27.92/18.13  #Subsume      : 6296
% 27.92/18.13  #Demod        : 3249
% 27.92/18.13  #Tautology    : 637
% 27.92/18.13  #SimpNegUnit  : 624
% 27.92/18.13  #BackRed      : 6
% 27.92/18.13  
% 27.92/18.13  #Partial instantiations: 0
% 27.92/18.13  #Strategies tried      : 1
% 27.92/18.13  
% 27.92/18.13  Timing (in seconds)
% 27.92/18.13  ----------------------
% 27.92/18.14  Preprocessing        : 0.50
% 27.92/18.14  Parsing              : 0.25
% 27.92/18.14  CNF conversion       : 0.08
% 27.92/18.14  Main loop            : 16.79
% 27.92/18.14  Inferencing          : 2.30
% 27.92/18.14  Reduction            : 3.94
% 27.92/18.14  Demodulation         : 2.70
% 27.92/18.14  BG Simplification    : 0.21
% 27.92/18.14  Subsumption          : 9.38
% 27.92/18.14  Abstraction          : 0.34
% 27.92/18.14  MUC search           : 0.00
% 27.92/18.14  Cooper               : 0.00
% 27.92/18.14  Total                : 17.35
% 27.92/18.14  Index Insertion      : 0.00
% 27.92/18.14  Index Deletion       : 0.00
% 27.92/18.14  Index Matching       : 0.00
% 27.92/18.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
