%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:32 EST 2020

% Result     : Theorem 24.73s
% Output     : CNFRefutation 24.73s
% Verified   : 
% Statistics : Number of formulae       :  193 (4425 expanded)
%              Number of leaves         :   57 (1552 expanded)
%              Depth                    :   26
%              Number of atoms          :  566 (25398 expanded)
%              Number of equality atoms :   64 (4006 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_350,negated_conjecture,(
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
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_204,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_247,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_233,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_163,axiom,(
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
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_301,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

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

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_229,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_222,axiom,(
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

tff(f_289,axiom,(
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
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_100,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_104,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_106,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_137,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_106])).

tff(c_130,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_128,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_126,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_116,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_132,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_118,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_160,plain,(
    ! [B_312,A_313] :
      ( l1_pre_topc(B_312)
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_169,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_160])).

tff(c_176,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_169])).

tff(c_110,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_122,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_244,plain,(
    ! [B_326,A_327] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_326),u1_pre_topc(B_326)))
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_248,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_244])).

tff(c_254,plain,(
    v1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_110,c_248])).

tff(c_12,plain,(
    ! [A_5] :
      ( g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) = A_5
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_166,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_160])).

tff(c_173,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_166])).

tff(c_58,plain,(
    ! [A_29] :
      ( m1_subset_1(u1_pre_topc(A_29),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29))))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_585,plain,(
    ! [D_347,B_348,C_349,A_350] :
      ( D_347 = B_348
      | g1_pre_topc(C_349,D_347) != g1_pre_topc(A_350,B_348)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(k1_zfmisc_1(A_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_593,plain,(
    ! [D_347,C_349] :
      ( u1_pre_topc('#skF_6') = D_347
      | g1_pre_topc(C_349,D_347) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_585])).

tff(c_615,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_618,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_615])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_618])).

tff(c_628,plain,(
    ! [D_356,C_357] :
      ( u1_pre_topc('#skF_6') = D_356
      | g1_pre_topc(C_357,D_356) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_645,plain,(
    ! [A_358] :
      ( u1_pre_topc(A_358) = u1_pre_topc('#skF_6')
      | A_358 != '#skF_7'
      | ~ v1_pre_topc(A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_628])).

tff(c_654,plain,
    ( u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_254,c_645])).

tff(c_661,plain,(
    u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_654])).

tff(c_703,plain,
    ( g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) = '#skF_7'
    | ~ v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_12])).

tff(c_722,plain,(
    g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_254,c_703])).

tff(c_627,plain,(
    m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_666,plain,(
    ! [C_359,A_360,D_361,B_362] :
      ( C_359 = A_360
      | g1_pre_topc(C_359,D_361) != g1_pre_topc(A_360,B_362)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(k1_zfmisc_1(A_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_674,plain,(
    ! [C_359,D_361] :
      ( u1_struct_0('#skF_6') = C_359
      | g1_pre_topc(C_359,D_361) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_666])).

tff(c_789,plain,(
    ! [C_367,D_368] :
      ( u1_struct_0('#skF_6') = C_367
      | g1_pre_topc(C_367,D_368) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_674])).

tff(c_799,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_789])).

tff(c_114,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_808,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_114])).

tff(c_134,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1355,plain,(
    ! [B_394,C_395,A_396] :
      ( m1_pre_topc(B_394,C_395)
      | ~ r1_tarski(u1_struct_0(B_394),u1_struct_0(C_395))
      | ~ m1_pre_topc(C_395,A_396)
      | ~ m1_pre_topc(B_394,A_396)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_1377,plain,(
    ! [B_397,A_398] :
      ( m1_pre_topc(B_397,B_397)
      | ~ m1_pre_topc(B_397,A_398)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398) ) ),
    inference(resolution,[status(thm)],[c_6,c_1355])).

tff(c_1399,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_1377])).

tff(c_1424,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_1399])).

tff(c_88,plain,(
    ! [A_108] :
      ( m1_pre_topc(A_108,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_263,plain,(
    ! [B_328,A_329] :
      ( m1_pre_topc(B_328,A_329)
      | ~ m1_pre_topc(B_328,g1_pre_topc(u1_struct_0(A_329),u1_pre_topc(A_329)))
      | ~ l1_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_269,plain,(
    ! [B_328] :
      ( m1_pre_topc(B_328,'#skF_6')
      | ~ m1_pre_topc(B_328,'#skF_7')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_263])).

tff(c_277,plain,(
    ! [B_330] :
      ( m1_pre_topc(B_330,'#skF_6')
      | ~ m1_pre_topc(B_330,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_269])).

tff(c_281,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_277])).

tff(c_284,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_281])).

tff(c_124,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_197,plain,(
    ! [B_319,A_320] :
      ( v2_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_203,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_197])).

tff(c_210,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_203])).

tff(c_112,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_807,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_112])).

tff(c_7824,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( k2_partfun1(u1_struct_0(A_588),u1_struct_0(B_589),C_590,u1_struct_0(D_591)) = k2_tmap_1(A_588,B_589,C_590,D_591)
      | ~ m1_pre_topc(D_591,A_588)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_588),u1_struct_0(B_589))))
      | ~ v1_funct_2(C_590,u1_struct_0(A_588),u1_struct_0(B_589))
      | ~ v1_funct_1(C_590)
      | ~ l1_pre_topc(B_589)
      | ~ v2_pre_topc(B_589)
      | v2_struct_0(B_589)
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588)
      | v2_struct_0(A_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_7826,plain,(
    ! [D_591] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_591)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_591)
      | ~ m1_pre_topc(D_591,'#skF_6')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_807,c_7824])).

tff(c_7836,plain,(
    ! [D_591] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_591)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_591)
      | ~ m1_pre_topc(D_591,'#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_173,c_128,c_126,c_116,c_808,c_7826])).

tff(c_8044,plain,(
    ! [D_594] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_594)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_594)
      | ~ m1_pre_topc(D_594,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_130,c_7836])).

tff(c_8053,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_8044])).

tff(c_8057,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_8053])).

tff(c_7837,plain,(
    ! [D_591] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_591)) = k2_tmap_1('#skF_6','#skF_5','#skF_8',D_591)
      | ~ m1_pre_topc(D_591,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_130,c_7836])).

tff(c_8168,plain,
    ( k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8057,c_7837])).

tff(c_8175,plain,(
    k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_7') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_8168])).

tff(c_8179,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8175,c_8057])).

tff(c_151,plain,(
    ! [A_310,B_311] :
      ( r1_tarski(A_310,B_311)
      | ~ m1_subset_1(A_310,k1_zfmisc_1(B_311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_112,c_151])).

tff(c_806,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_159])).

tff(c_136,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_431,plain,(
    ! [C_339,A_340,B_341] :
      ( m1_pre_topc(C_339,A_340)
      | ~ m1_pre_topc(C_339,B_341)
      | ~ m1_pre_topc(B_341,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_451,plain,(
    ! [A_340] :
      ( m1_pre_topc('#skF_6',A_340)
      | ~ m1_pre_topc('#skF_4',A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(resolution,[status(thm)],[c_122,c_431])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8201,plain,(
    ! [A_599,B_598,D_600,E_596,C_597] :
      ( k3_tmap_1(A_599,B_598,C_597,D_600,E_596) = k2_partfun1(u1_struct_0(C_597),u1_struct_0(B_598),E_596,u1_struct_0(D_600))
      | ~ m1_pre_topc(D_600,C_597)
      | ~ m1_subset_1(E_596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597),u1_struct_0(B_598))))
      | ~ v1_funct_2(E_596,u1_struct_0(C_597),u1_struct_0(B_598))
      | ~ v1_funct_1(E_596)
      | ~ m1_pre_topc(D_600,A_599)
      | ~ m1_pre_topc(C_597,A_599)
      | ~ l1_pre_topc(B_598)
      | ~ v2_pre_topc(B_598)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(A_599)
      | ~ v2_pre_topc(A_599)
      | v2_struct_0(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_21896,plain,(
    ! [D_803,B_806,A_802,A_804,C_805] :
      ( k3_tmap_1(A_802,B_806,C_805,D_803,A_804) = k2_partfun1(u1_struct_0(C_805),u1_struct_0(B_806),A_804,u1_struct_0(D_803))
      | ~ m1_pre_topc(D_803,C_805)
      | ~ v1_funct_2(A_804,u1_struct_0(C_805),u1_struct_0(B_806))
      | ~ v1_funct_1(A_804)
      | ~ m1_pre_topc(D_803,A_802)
      | ~ m1_pre_topc(C_805,A_802)
      | ~ l1_pre_topc(B_806)
      | ~ v2_pre_topc(B_806)
      | v2_struct_0(B_806)
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802)
      | ~ r1_tarski(A_804,k2_zfmisc_1(u1_struct_0(C_805),u1_struct_0(B_806))) ) ),
    inference(resolution,[status(thm)],[c_10,c_8201])).

tff(c_61504,plain,(
    ! [A_1219,B_1220,C_1221,A_1222] :
      ( k3_tmap_1(A_1219,B_1220,C_1221,'#skF_6',A_1222) = k2_partfun1(u1_struct_0(C_1221),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',C_1221)
      | ~ v1_funct_2(A_1222,u1_struct_0(C_1221),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ m1_pre_topc(C_1221,A_1219)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | v2_struct_0(A_1219)
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0(C_1221),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4',A_1219)
      | ~ l1_pre_topc(A_1219)
      | ~ v2_pre_topc(A_1219) ) ),
    inference(resolution,[status(thm)],[c_451,c_21896])).

tff(c_61642,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_6','#skF_6',A_1222)
      | ~ m1_pre_topc('#skF_6','#skF_6')
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_6'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122,c_61504])).

tff(c_61852,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_6','#skF_6',A_1222)
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_6'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_1424,c_61642])).

tff(c_61853,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_6','#skF_6',A_1222)
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_6'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_61852])).

tff(c_65339,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61853])).

tff(c_65342,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_65339])).

tff(c_65346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_65342])).

tff(c_65348,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_61853])).

tff(c_899,plain,(
    ! [A_369,B_370] :
      ( m1_pre_topc(A_369,g1_pre_topc(u1_struct_0(B_370),u1_pre_topc(B_370)))
      | ~ m1_pre_topc(A_369,B_370)
      | ~ l1_pre_topc(B_370)
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_926,plain,(
    ! [A_369] :
      ( m1_pre_topc(A_369,'#skF_7')
      | ~ m1_pre_topc(A_369,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_369) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_899])).

tff(c_938,plain,(
    ! [A_369] :
      ( m1_pre_topc(A_369,'#skF_7')
      | ~ m1_pre_topc(A_369,'#skF_6')
      | ~ l1_pre_topc(A_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_926])).

tff(c_206,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_197])).

tff(c_213,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_206])).

tff(c_50,plain,(
    ! [A_9] :
      ( r2_hidden(u1_struct_0(A_9),u1_pre_topc(A_9))
      | ~ v2_pre_topc(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_712,plain,
    ( r2_hidden(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_50])).

tff(c_728,plain,(
    r2_hidden(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_213,c_712])).

tff(c_804,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_728])).

tff(c_86,plain,(
    ! [B_107,A_105] :
      ( m1_subset_1(u1_struct_0(B_107),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc(B_107,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_846,plain,(
    ! [A_105] :
      ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_pre_topc('#skF_7',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_86])).

tff(c_1049,plain,(
    ! [B_375,A_376] :
      ( v3_pre_topc(B_375,A_376)
      | ~ r2_hidden(B_375,u1_pre_topc(A_376))
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ l1_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1055,plain,(
    ! [B_375] :
      ( v3_pre_topc(B_375,'#skF_7')
      | ~ r2_hidden(B_375,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_1049])).

tff(c_1325,plain,(
    ! [B_393] :
      ( v3_pre_topc(B_393,'#skF_7')
      | ~ r2_hidden(B_393,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_661,c_1055])).

tff(c_1329,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_846,c_1325])).

tff(c_1346,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_284,c_804,c_1329])).

tff(c_3125,plain,(
    ! [B_458,A_459] :
      ( v1_tsep_1(B_458,A_459)
      | ~ v3_pre_topc(u1_struct_0(B_458),A_459)
      | ~ m1_subset_1(u1_struct_0(B_458),k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ m1_pre_topc(B_458,A_459)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_3194,plain,(
    ! [B_462,A_463] :
      ( v1_tsep_1(B_462,A_463)
      | ~ v3_pre_topc(u1_struct_0(B_462),A_463)
      | ~ v2_pre_topc(A_463)
      | ~ m1_pre_topc(B_462,A_463)
      | ~ l1_pre_topc(A_463) ) ),
    inference(resolution,[status(thm)],[c_86,c_3125])).

tff(c_3215,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_1346,c_3194])).

tff(c_3238,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_213,c_3215])).

tff(c_3242,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3238])).

tff(c_3245,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_938,c_3242])).

tff(c_3252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1424,c_3245])).

tff(c_3254,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3238])).

tff(c_61644,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_7'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_7','#skF_6',A_1222)
      | ~ m1_pre_topc('#skF_6','#skF_7')
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_7'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_118,c_61504])).

tff(c_61856,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_7','#skF_6',A_1222)
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_6'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_132,c_799,c_799,c_3254,c_799,c_61644])).

tff(c_61857,plain,(
    ! [B_1220,A_1222] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1220),A_1222,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1220,'#skF_7','#skF_6',A_1222)
      | ~ v1_funct_2(A_1222,u1_struct_0('#skF_6'),u1_struct_0(B_1220))
      | ~ v1_funct_1(A_1222)
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220)
      | v2_struct_0(B_1220)
      | ~ r1_tarski(A_1222,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1220)))
      | ~ m1_pre_topc('#skF_4','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_61856])).

tff(c_71435,plain,(
    ! [B_1273,A_1274] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_1273),A_1274,u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4',B_1273,'#skF_7','#skF_6',A_1274)
      | ~ v1_funct_2(A_1274,u1_struct_0('#skF_6'),u1_struct_0(B_1273))
      | ~ v1_funct_1(A_1274)
      | ~ l1_pre_topc(B_1273)
      | ~ v2_pre_topc(B_1273)
      | v2_struct_0(B_1273)
      | ~ r1_tarski(A_1274,k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_1273))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65348,c_61857])).

tff(c_71459,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0('#skF_6')) = k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_806,c_71435])).

tff(c_71471,plain,
    ( k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_116,c_808,c_8179,c_71459])).

tff(c_71472,plain,(
    k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_71471])).

tff(c_102,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_138,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102])).

tff(c_72288,plain,(
    r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71472,c_138])).

tff(c_120,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_350])).

tff(c_3253,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3238])).

tff(c_7828,plain,(
    ! [B_589,C_590,D_591] :
      ( k2_partfun1(u1_struct_0('#skF_7'),u1_struct_0(B_589),C_590,u1_struct_0(D_591)) = k2_tmap_1('#skF_7',B_589,C_590,D_591)
      | ~ m1_pre_topc(D_591,'#skF_7')
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_589))))
      | ~ v1_funct_2(C_590,u1_struct_0('#skF_7'),u1_struct_0(B_589))
      | ~ v1_funct_1(C_590)
      | ~ l1_pre_topc(B_589)
      | ~ v2_pre_topc(B_589)
      | v2_struct_0(B_589)
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_7824])).

tff(c_7839,plain,(
    ! [B_589,C_590,D_591] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_589),C_590,u1_struct_0(D_591)) = k2_tmap_1('#skF_7',B_589,C_590,D_591)
      | ~ m1_pre_topc(D_591,'#skF_7')
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_589))))
      | ~ v1_funct_2(C_590,u1_struct_0('#skF_6'),u1_struct_0(B_589))
      | ~ v1_funct_1(C_590)
      | ~ l1_pre_topc(B_589)
      | ~ v2_pre_topc(B_589)
      | v2_struct_0(B_589)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_176,c_799,c_799,c_7828])).

tff(c_14214,plain,(
    ! [B_695,C_696,D_697] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0(B_695),C_696,u1_struct_0(D_697)) = k2_tmap_1('#skF_7',B_695,C_696,D_697)
      | ~ m1_pre_topc(D_697,'#skF_7')
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0(B_695))))
      | ~ v1_funct_2(C_696,u1_struct_0('#skF_6'),u1_struct_0(B_695))
      | ~ v1_funct_1(C_696)
      | ~ l1_pre_topc(B_695)
      | ~ v2_pre_topc(B_695)
      | v2_struct_0(B_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_7839])).

tff(c_14216,plain,(
    ! [D_697] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_697)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_697)
      | ~ m1_pre_topc(D_697,'#skF_7')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_807,c_14214])).

tff(c_14224,plain,(
    ! [D_697] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_697)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_697)
      | ~ m1_pre_topc(D_697,'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_116,c_808,c_14216])).

tff(c_14230,plain,(
    ! [D_698] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'),'#skF_8',u1_struct_0(D_698)) = k2_tmap_1('#skF_7','#skF_5','#skF_8',D_698)
      | ~ m1_pre_topc(D_698,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_14224])).

tff(c_14251,plain,
    ( k2_tmap_1('#skF_7','#skF_5','#skF_8','#skF_6') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14230,c_8179])).

tff(c_14284,plain,(
    k2_tmap_1('#skF_7','#skF_5','#skF_8','#skF_6') = k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_14251])).

tff(c_94,plain,(
    ! [B_148,A_116,F_178,D_172,C_164] :
      ( r1_tmap_1(B_148,A_116,C_164,F_178)
      | ~ r1_tmap_1(D_172,A_116,k2_tmap_1(B_148,A_116,C_164,D_172),F_178)
      | ~ m1_subset_1(F_178,u1_struct_0(D_172))
      | ~ m1_subset_1(F_178,u1_struct_0(B_148))
      | ~ m1_pre_topc(D_172,B_148)
      | ~ v1_tsep_1(D_172,B_148)
      | v2_struct_0(D_172)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_148),u1_struct_0(A_116))))
      | ~ v1_funct_2(C_164,u1_struct_0(B_148),u1_struct_0(A_116))
      | ~ v1_funct_1(C_164)
      | ~ l1_pre_topc(B_148)
      | ~ v2_pre_topc(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_14301,plain,(
    ! [F_178] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_178)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_178)
      | ~ m1_subset_1(F_178,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_178,u1_struct_0('#skF_7'))
      | ~ m1_pre_topc('#skF_6','#skF_7')
      | ~ v1_tsep_1('#skF_6','#skF_7')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14284,c_94])).

tff(c_14305,plain,(
    ! [F_178] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_178)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_178)
      | ~ m1_subset_1(F_178,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_213,c_176,c_116,c_808,c_799,c_807,c_799,c_3253,c_3254,c_799,c_14301])).

tff(c_14306,plain,(
    ! [F_178] :
      ( r1_tmap_1('#skF_7','#skF_5','#skF_8',F_178)
      | ~ r1_tmap_1('#skF_6','#skF_5',k2_tmap_1('#skF_6','#skF_5','#skF_8','#skF_6'),F_178)
      | ~ m1_subset_1(F_178,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_120,c_124,c_14305])).

tff(c_72295,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_72288,c_14306])).

tff(c_72300,plain,(
    r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72295])).

tff(c_72302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_72300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.73/14.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/14.62  
% 24.73/14.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/14.63  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 24.73/14.63  
% 24.73/14.63  %Foreground sorts:
% 24.73/14.63  
% 24.73/14.63  
% 24.73/14.63  %Background operators:
% 24.73/14.63  
% 24.73/14.63  
% 24.73/14.63  %Foreground operators:
% 24.73/14.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.73/14.63  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 24.73/14.63  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 24.73/14.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 24.73/14.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 24.73/14.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 24.73/14.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.73/14.63  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 24.73/14.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.73/14.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 24.73/14.63  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 24.73/14.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.73/14.63  tff('#skF_7', type, '#skF_7': $i).
% 24.73/14.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.73/14.63  tff('#skF_10', type, '#skF_10': $i).
% 24.73/14.63  tff('#skF_5', type, '#skF_5': $i).
% 24.73/14.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 24.73/14.63  tff('#skF_6', type, '#skF_6': $i).
% 24.73/14.63  tff('#skF_9', type, '#skF_9': $i).
% 24.73/14.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 24.73/14.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.73/14.63  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 24.73/14.63  tff('#skF_8', type, '#skF_8': $i).
% 24.73/14.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.73/14.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.73/14.63  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 24.73/14.63  tff('#skF_4', type, '#skF_4': $i).
% 24.73/14.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 24.73/14.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.73/14.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 24.73/14.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 24.73/14.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.73/14.63  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 24.73/14.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.73/14.63  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 24.73/14.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.73/14.63  
% 24.73/14.66  tff(f_350, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 24.73/14.66  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 24.73/14.66  tff(f_204, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 24.73/14.66  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 24.73/14.66  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 24.73/14.66  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 24.73/14.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.73/14.66  tff(f_247, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 24.73/14.66  tff(f_233, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 24.73/14.66  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 24.73/14.66  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 24.73/14.66  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 24.73/14.66  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 24.73/14.66  tff(f_301, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 24.73/14.66  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 24.73/14.66  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 24.73/14.66  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 24.73/14.66  tff(f_229, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 24.73/14.66  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 24.73/14.66  tff(f_222, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 24.73/14.66  tff(f_289, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 24.73/14.66  tff(c_100, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_104, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_106, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_137, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_106])).
% 24.73/14.66  tff(c_130, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_128, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_126, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_116, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_132, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_118, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_160, plain, (![B_312, A_313]: (l1_pre_topc(B_312) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_91])).
% 24.73/14.66  tff(c_169, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_118, c_160])).
% 24.73/14.66  tff(c_176, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_169])).
% 24.73/14.66  tff(c_110, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_122, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_244, plain, (![B_326, A_327]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_326), u1_pre_topc(B_326))) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_204])).
% 24.73/14.66  tff(c_248, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_122, c_244])).
% 24.73/14.66  tff(c_254, plain, (v1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_110, c_248])).
% 24.73/14.66  tff(c_12, plain, (![A_5]: (g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))=A_5 | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.73/14.66  tff(c_166, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_122, c_160])).
% 24.73/14.66  tff(c_173, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_166])).
% 24.73/14.66  tff(c_58, plain, (![A_29]: (m1_subset_1(u1_pre_topc(A_29), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_29)))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 24.73/14.66  tff(c_585, plain, (![D_347, B_348, C_349, A_350]: (D_347=B_348 | g1_pre_topc(C_349, D_347)!=g1_pre_topc(A_350, B_348) | ~m1_subset_1(B_348, k1_zfmisc_1(k1_zfmisc_1(A_350))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.73/14.66  tff(c_593, plain, (![D_347, C_349]: (u1_pre_topc('#skF_6')=D_347 | g1_pre_topc(C_349, D_347)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_585])).
% 24.73/14.66  tff(c_615, plain, (~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_593])).
% 24.73/14.66  tff(c_618, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_58, c_615])).
% 24.73/14.66  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_618])).
% 24.73/14.66  tff(c_628, plain, (![D_356, C_357]: (u1_pre_topc('#skF_6')=D_356 | g1_pre_topc(C_357, D_356)!='#skF_7')), inference(splitRight, [status(thm)], [c_593])).
% 24.73/14.66  tff(c_645, plain, (![A_358]: (u1_pre_topc(A_358)=u1_pre_topc('#skF_6') | A_358!='#skF_7' | ~v1_pre_topc(A_358) | ~l1_pre_topc(A_358))), inference(superposition, [status(thm), theory('equality')], [c_12, c_628])).
% 24.73/14.66  tff(c_654, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_254, c_645])).
% 24.73/14.66  tff(c_661, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_654])).
% 24.73/14.66  tff(c_703, plain, (g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))='#skF_7' | ~v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_661, c_12])).
% 24.73/14.66  tff(c_722, plain, (g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_254, c_703])).
% 24.73/14.66  tff(c_627, plain, (m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_593])).
% 24.73/14.66  tff(c_666, plain, (![C_359, A_360, D_361, B_362]: (C_359=A_360 | g1_pre_topc(C_359, D_361)!=g1_pre_topc(A_360, B_362) | ~m1_subset_1(B_362, k1_zfmisc_1(k1_zfmisc_1(A_360))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 24.73/14.66  tff(c_674, plain, (![C_359, D_361]: (u1_struct_0('#skF_6')=C_359 | g1_pre_topc(C_359, D_361)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_110, c_666])).
% 24.73/14.66  tff(c_789, plain, (![C_367, D_368]: (u1_struct_0('#skF_6')=C_367 | g1_pre_topc(C_367, D_368)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_674])).
% 24.73/14.66  tff(c_799, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_722, c_789])).
% 24.73/14.66  tff(c_114, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_808, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_114])).
% 24.73/14.66  tff(c_134, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.73/14.66  tff(c_1355, plain, (![B_394, C_395, A_396]: (m1_pre_topc(B_394, C_395) | ~r1_tarski(u1_struct_0(B_394), u1_struct_0(C_395)) | ~m1_pre_topc(C_395, A_396) | ~m1_pre_topc(B_394, A_396) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396))), inference(cnfTransformation, [status(thm)], [f_247])).
% 24.73/14.66  tff(c_1377, plain, (![B_397, A_398]: (m1_pre_topc(B_397, B_397) | ~m1_pre_topc(B_397, A_398) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398))), inference(resolution, [status(thm)], [c_6, c_1355])).
% 24.73/14.66  tff(c_1399, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_122, c_1377])).
% 24.73/14.66  tff(c_1424, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_1399])).
% 24.73/14.66  tff(c_88, plain, (![A_108]: (m1_pre_topc(A_108, A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_233])).
% 24.73/14.66  tff(c_263, plain, (![B_328, A_329]: (m1_pre_topc(B_328, A_329) | ~m1_pre_topc(B_328, g1_pre_topc(u1_struct_0(A_329), u1_pre_topc(A_329))) | ~l1_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_127])).
% 24.73/14.66  tff(c_269, plain, (![B_328]: (m1_pre_topc(B_328, '#skF_6') | ~m1_pre_topc(B_328, '#skF_7') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_263])).
% 24.73/14.66  tff(c_277, plain, (![B_330]: (m1_pre_topc(B_330, '#skF_6') | ~m1_pre_topc(B_330, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_269])).
% 24.73/14.66  tff(c_281, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_88, c_277])).
% 24.73/14.66  tff(c_284, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_281])).
% 24.73/14.66  tff(c_124, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_197, plain, (![B_319, A_320]: (v2_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_50])).
% 24.73/14.66  tff(c_203, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_122, c_197])).
% 24.73/14.66  tff(c_210, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_203])).
% 24.73/14.66  tff(c_112, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_807, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_112])).
% 24.73/14.66  tff(c_7824, plain, (![A_588, B_589, C_590, D_591]: (k2_partfun1(u1_struct_0(A_588), u1_struct_0(B_589), C_590, u1_struct_0(D_591))=k2_tmap_1(A_588, B_589, C_590, D_591) | ~m1_pre_topc(D_591, A_588) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_588), u1_struct_0(B_589)))) | ~v1_funct_2(C_590, u1_struct_0(A_588), u1_struct_0(B_589)) | ~v1_funct_1(C_590) | ~l1_pre_topc(B_589) | ~v2_pre_topc(B_589) | v2_struct_0(B_589) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588) | v2_struct_0(A_588))), inference(cnfTransformation, [status(thm)], [f_163])).
% 24.73/14.66  tff(c_7826, plain, (![D_591]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_591))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_591) | ~m1_pre_topc(D_591, '#skF_6') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_807, c_7824])).
% 24.73/14.66  tff(c_7836, plain, (![D_591]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_591))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_591) | ~m1_pre_topc(D_591, '#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_173, c_128, c_126, c_116, c_808, c_7826])).
% 24.73/14.66  tff(c_8044, plain, (![D_594]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_594))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_594) | ~m1_pre_topc(D_594, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_124, c_130, c_7836])).
% 24.73/14.66  tff(c_8053, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_799, c_8044])).
% 24.73/14.66  tff(c_8057, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_8053])).
% 24.73/14.66  tff(c_7837, plain, (![D_591]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_591))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', D_591) | ~m1_pre_topc(D_591, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_124, c_130, c_7836])).
% 24.73/14.66  tff(c_8168, plain, (k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8057, c_7837])).
% 24.73/14.66  tff(c_8175, plain, (k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_7')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_8168])).
% 24.73/14.66  tff(c_8179, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8175, c_8057])).
% 24.73/14.66  tff(c_151, plain, (![A_310, B_311]: (r1_tarski(A_310, B_311) | ~m1_subset_1(A_310, k1_zfmisc_1(B_311)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.73/14.66  tff(c_159, plain, (r1_tarski('#skF_8', k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_112, c_151])).
% 24.73/14.66  tff(c_806, plain, (r1_tarski('#skF_8', k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_159])).
% 24.73/14.66  tff(c_136, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_431, plain, (![C_339, A_340, B_341]: (m1_pre_topc(C_339, A_340) | ~m1_pre_topc(C_339, B_341) | ~m1_pre_topc(B_341, A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_301])).
% 24.73/14.66  tff(c_451, plain, (![A_340]: (m1_pre_topc('#skF_6', A_340) | ~m1_pre_topc('#skF_4', A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(resolution, [status(thm)], [c_122, c_431])).
% 24.73/14.66  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.73/14.66  tff(c_8201, plain, (![A_599, B_598, D_600, E_596, C_597]: (k3_tmap_1(A_599, B_598, C_597, D_600, E_596)=k2_partfun1(u1_struct_0(C_597), u1_struct_0(B_598), E_596, u1_struct_0(D_600)) | ~m1_pre_topc(D_600, C_597) | ~m1_subset_1(E_596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_597), u1_struct_0(B_598)))) | ~v1_funct_2(E_596, u1_struct_0(C_597), u1_struct_0(B_598)) | ~v1_funct_1(E_596) | ~m1_pre_topc(D_600, A_599) | ~m1_pre_topc(C_597, A_599) | ~l1_pre_topc(B_598) | ~v2_pre_topc(B_598) | v2_struct_0(B_598) | ~l1_pre_topc(A_599) | ~v2_pre_topc(A_599) | v2_struct_0(A_599))), inference(cnfTransformation, [status(thm)], [f_195])).
% 24.73/14.66  tff(c_21896, plain, (![D_803, B_806, A_802, A_804, C_805]: (k3_tmap_1(A_802, B_806, C_805, D_803, A_804)=k2_partfun1(u1_struct_0(C_805), u1_struct_0(B_806), A_804, u1_struct_0(D_803)) | ~m1_pre_topc(D_803, C_805) | ~v1_funct_2(A_804, u1_struct_0(C_805), u1_struct_0(B_806)) | ~v1_funct_1(A_804) | ~m1_pre_topc(D_803, A_802) | ~m1_pre_topc(C_805, A_802) | ~l1_pre_topc(B_806) | ~v2_pre_topc(B_806) | v2_struct_0(B_806) | ~l1_pre_topc(A_802) | ~v2_pre_topc(A_802) | v2_struct_0(A_802) | ~r1_tarski(A_804, k2_zfmisc_1(u1_struct_0(C_805), u1_struct_0(B_806))))), inference(resolution, [status(thm)], [c_10, c_8201])).
% 24.73/14.66  tff(c_61504, plain, (![A_1219, B_1220, C_1221, A_1222]: (k3_tmap_1(A_1219, B_1220, C_1221, '#skF_6', A_1222)=k2_partfun1(u1_struct_0(C_1221), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', C_1221) | ~v1_funct_2(A_1222, u1_struct_0(C_1221), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~m1_pre_topc(C_1221, A_1219) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | v2_struct_0(A_1219) | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0(C_1221), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', A_1219) | ~l1_pre_topc(A_1219) | ~v2_pre_topc(A_1219))), inference(resolution, [status(thm)], [c_451, c_21896])).
% 24.73/14.66  tff(c_61642, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_6', '#skF_6', A_1222) | ~m1_pre_topc('#skF_6', '#skF_6') | ~v1_funct_2(A_1222, u1_struct_0('#skF_6'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | v2_struct_0('#skF_4') | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_122, c_61504])).
% 24.73/14.66  tff(c_61852, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_6', '#skF_6', A_1222) | ~v1_funct_2(A_1222, u1_struct_0('#skF_6'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | v2_struct_0('#skF_4') | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_1424, c_61642])).
% 24.73/14.66  tff(c_61853, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_6', '#skF_6', A_1222) | ~v1_funct_2(A_1222, u1_struct_0('#skF_6'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_136, c_61852])).
% 24.73/14.66  tff(c_65339, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_61853])).
% 24.73/14.66  tff(c_65342, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_88, c_65339])).
% 24.73/14.66  tff(c_65346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_65342])).
% 24.73/14.66  tff(c_65348, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_61853])).
% 24.73/14.66  tff(c_899, plain, (![A_369, B_370]: (m1_pre_topc(A_369, g1_pre_topc(u1_struct_0(B_370), u1_pre_topc(B_370))) | ~m1_pre_topc(A_369, B_370) | ~l1_pre_topc(B_370) | ~l1_pre_topc(A_369))), inference(cnfTransformation, [status(thm)], [f_136])).
% 24.73/14.66  tff(c_926, plain, (![A_369]: (m1_pre_topc(A_369, '#skF_7') | ~m1_pre_topc(A_369, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_369))), inference(superposition, [status(thm), theory('equality')], [c_110, c_899])).
% 24.73/14.66  tff(c_938, plain, (![A_369]: (m1_pre_topc(A_369, '#skF_7') | ~m1_pre_topc(A_369, '#skF_6') | ~l1_pre_topc(A_369))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_926])).
% 24.73/14.66  tff(c_206, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_118, c_197])).
% 24.73/14.66  tff(c_213, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_206])).
% 24.73/14.66  tff(c_50, plain, (![A_9]: (r2_hidden(u1_struct_0(A_9), u1_pre_topc(A_9)) | ~v2_pre_topc(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_75])).
% 24.73/14.66  tff(c_712, plain, (r2_hidden(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_661, c_50])).
% 24.73/14.66  tff(c_728, plain, (r2_hidden(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_213, c_712])).
% 24.73/14.66  tff(c_804, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_728])).
% 24.73/14.66  tff(c_86, plain, (![B_107, A_105]: (m1_subset_1(u1_struct_0(B_107), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc(B_107, A_105) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_229])).
% 24.73/14.66  tff(c_846, plain, (![A_105]: (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_pre_topc('#skF_7', A_105) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_799, c_86])).
% 24.73/14.66  tff(c_1049, plain, (![B_375, A_376]: (v3_pre_topc(B_375, A_376) | ~r2_hidden(B_375, u1_pre_topc(A_376)) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0(A_376))) | ~l1_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.73/14.66  tff(c_1055, plain, (![B_375]: (v3_pre_topc(B_375, '#skF_7') | ~r2_hidden(B_375, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_799, c_1049])).
% 24.73/14.66  tff(c_1325, plain, (![B_393]: (v3_pre_topc(B_393, '#skF_7') | ~r2_hidden(B_393, u1_pre_topc('#skF_6')) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_661, c_1055])).
% 24.73/14.66  tff(c_1329, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_846, c_1325])).
% 24.73/14.66  tff(c_1346, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_284, c_804, c_1329])).
% 24.73/14.66  tff(c_3125, plain, (![B_458, A_459]: (v1_tsep_1(B_458, A_459) | ~v3_pre_topc(u1_struct_0(B_458), A_459) | ~m1_subset_1(u1_struct_0(B_458), k1_zfmisc_1(u1_struct_0(A_459))) | ~m1_pre_topc(B_458, A_459) | ~l1_pre_topc(A_459) | ~v2_pre_topc(A_459))), inference(cnfTransformation, [status(thm)], [f_222])).
% 24.73/14.66  tff(c_3194, plain, (![B_462, A_463]: (v1_tsep_1(B_462, A_463) | ~v3_pre_topc(u1_struct_0(B_462), A_463) | ~v2_pre_topc(A_463) | ~m1_pre_topc(B_462, A_463) | ~l1_pre_topc(A_463))), inference(resolution, [status(thm)], [c_86, c_3125])).
% 24.73/14.66  tff(c_3215, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_1346, c_3194])).
% 24.73/14.66  tff(c_3238, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_213, c_3215])).
% 24.73/14.66  tff(c_3242, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_3238])).
% 24.73/14.66  tff(c_3245, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_938, c_3242])).
% 24.73/14.66  tff(c_3252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_1424, c_3245])).
% 24.73/14.66  tff(c_3254, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_3238])).
% 24.73/14.66  tff(c_61644, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_7'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_7', '#skF_6', A_1222) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_funct_2(A_1222, u1_struct_0('#skF_7'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | v2_struct_0('#skF_4') | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_118, c_61504])).
% 24.73/14.66  tff(c_61856, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_7', '#skF_6', A_1222) | ~v1_funct_2(A_1222, u1_struct_0('#skF_6'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | v2_struct_0('#skF_4') | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_132, c_799, c_799, c_3254, c_799, c_61644])).
% 24.73/14.66  tff(c_61857, plain, (![B_1220, A_1222]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1220), A_1222, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1220, '#skF_7', '#skF_6', A_1222) | ~v1_funct_2(A_1222, u1_struct_0('#skF_6'), u1_struct_0(B_1220)) | ~v1_funct_1(A_1222) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220) | v2_struct_0(B_1220) | ~r1_tarski(A_1222, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1220))) | ~m1_pre_topc('#skF_4', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_136, c_61856])).
% 24.73/14.66  tff(c_71435, plain, (![B_1273, A_1274]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_1273), A_1274, u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', B_1273, '#skF_7', '#skF_6', A_1274) | ~v1_funct_2(A_1274, u1_struct_0('#skF_6'), u1_struct_0(B_1273)) | ~v1_funct_1(A_1274) | ~l1_pre_topc(B_1273) | ~v2_pre_topc(B_1273) | v2_struct_0(B_1273) | ~r1_tarski(A_1274, k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_1273))))), inference(demodulation, [status(thm), theory('equality')], [c_65348, c_61857])).
% 24.73/14.66  tff(c_71459, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0('#skF_6'))=k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_806, c_71435])).
% 24.73/14.66  tff(c_71471, plain, (k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_126, c_116, c_808, c_8179, c_71459])).
% 24.73/14.66  tff(c_71472, plain, (k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_130, c_71471])).
% 24.73/14.66  tff(c_102, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_138, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102])).
% 24.73/14.66  tff(c_72288, plain, (r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_71472, c_138])).
% 24.73/14.66  tff(c_120, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_350])).
% 24.73/14.66  tff(c_3253, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_3238])).
% 24.73/14.66  tff(c_7828, plain, (![B_589, C_590, D_591]: (k2_partfun1(u1_struct_0('#skF_7'), u1_struct_0(B_589), C_590, u1_struct_0(D_591))=k2_tmap_1('#skF_7', B_589, C_590, D_591) | ~m1_pre_topc(D_591, '#skF_7') | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_589)))) | ~v1_funct_2(C_590, u1_struct_0('#skF_7'), u1_struct_0(B_589)) | ~v1_funct_1(C_590) | ~l1_pre_topc(B_589) | ~v2_pre_topc(B_589) | v2_struct_0(B_589) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_799, c_7824])).
% 24.73/14.66  tff(c_7839, plain, (![B_589, C_590, D_591]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_589), C_590, u1_struct_0(D_591))=k2_tmap_1('#skF_7', B_589, C_590, D_591) | ~m1_pre_topc(D_591, '#skF_7') | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_589)))) | ~v1_funct_2(C_590, u1_struct_0('#skF_6'), u1_struct_0(B_589)) | ~v1_funct_1(C_590) | ~l1_pre_topc(B_589) | ~v2_pre_topc(B_589) | v2_struct_0(B_589) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_176, c_799, c_799, c_7828])).
% 24.73/14.66  tff(c_14214, plain, (![B_695, C_696, D_697]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0(B_695), C_696, u1_struct_0(D_697))=k2_tmap_1('#skF_7', B_695, C_696, D_697) | ~m1_pre_topc(D_697, '#skF_7') | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0(B_695)))) | ~v1_funct_2(C_696, u1_struct_0('#skF_6'), u1_struct_0(B_695)) | ~v1_funct_1(C_696) | ~l1_pre_topc(B_695) | ~v2_pre_topc(B_695) | v2_struct_0(B_695))), inference(negUnitSimplification, [status(thm)], [c_120, c_7839])).
% 24.73/14.66  tff(c_14216, plain, (![D_697]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_697))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_697) | ~m1_pre_topc(D_697, '#skF_7') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_807, c_14214])).
% 24.73/14.66  tff(c_14224, plain, (![D_697]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_697))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_697) | ~m1_pre_topc(D_697, '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_126, c_116, c_808, c_14216])).
% 24.73/14.66  tff(c_14230, plain, (![D_698]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'), '#skF_8', u1_struct_0(D_698))=k2_tmap_1('#skF_7', '#skF_5', '#skF_8', D_698) | ~m1_pre_topc(D_698, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_130, c_14224])).
% 24.73/14.66  tff(c_14251, plain, (k2_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_6')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14230, c_8179])).
% 24.73/14.66  tff(c_14284, plain, (k2_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_6')=k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_14251])).
% 24.73/14.66  tff(c_94, plain, (![B_148, A_116, F_178, D_172, C_164]: (r1_tmap_1(B_148, A_116, C_164, F_178) | ~r1_tmap_1(D_172, A_116, k2_tmap_1(B_148, A_116, C_164, D_172), F_178) | ~m1_subset_1(F_178, u1_struct_0(D_172)) | ~m1_subset_1(F_178, u1_struct_0(B_148)) | ~m1_pre_topc(D_172, B_148) | ~v1_tsep_1(D_172, B_148) | v2_struct_0(D_172) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_148), u1_struct_0(A_116)))) | ~v1_funct_2(C_164, u1_struct_0(B_148), u1_struct_0(A_116)) | ~v1_funct_1(C_164) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_289])).
% 24.73/14.66  tff(c_14301, plain, (![F_178]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_178) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_178) | ~m1_subset_1(F_178, u1_struct_0('#skF_6')) | ~m1_subset_1(F_178, u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14284, c_94])).
% 24.73/14.66  tff(c_14305, plain, (![F_178]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_178) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_178) | ~m1_subset_1(F_178, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_126, c_213, c_176, c_116, c_808, c_799, c_807, c_799, c_3253, c_3254, c_799, c_14301])).
% 24.73/14.66  tff(c_14306, plain, (![F_178]: (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', F_178) | ~r1_tmap_1('#skF_6', '#skF_5', k2_tmap_1('#skF_6', '#skF_5', '#skF_8', '#skF_6'), F_178) | ~m1_subset_1(F_178, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_130, c_120, c_124, c_14305])).
% 24.73/14.66  tff(c_72295, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_72288, c_14306])).
% 24.73/14.66  tff(c_72300, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_72295])).
% 24.73/14.66  tff(c_72302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_72300])).
% 24.73/14.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.73/14.66  
% 24.73/14.66  Inference rules
% 24.73/14.66  ----------------------
% 24.73/14.66  #Ref     : 6
% 24.73/14.66  #Sup     : 16967
% 24.73/14.66  #Fact    : 0
% 24.73/14.66  #Define  : 0
% 24.73/14.66  #Split   : 11
% 24.73/14.66  #Chain   : 0
% 24.73/14.66  #Close   : 0
% 24.73/14.66  
% 24.73/14.66  Ordering : KBO
% 24.73/14.66  
% 24.73/14.66  Simplification rules
% 24.73/14.66  ----------------------
% 24.73/14.66  #Subsume      : 4966
% 24.73/14.66  #Demod        : 32798
% 24.73/14.66  #Tautology    : 3560
% 24.73/14.66  #SimpNegUnit  : 617
% 24.73/14.66  #BackRed      : 14
% 24.73/14.66  
% 24.73/14.66  #Partial instantiations: 0
% 24.73/14.66  #Strategies tried      : 1
% 24.73/14.66  
% 24.73/14.66  Timing (in seconds)
% 24.73/14.66  ----------------------
% 24.73/14.66  Preprocessing        : 0.45
% 24.73/14.66  Parsing              : 0.23
% 24.73/14.66  CNF conversion       : 0.05
% 24.73/14.66  Main loop            : 13.40
% 24.73/14.66  Inferencing          : 2.31
% 24.73/14.66  Reduction            : 4.53
% 24.73/14.66  Demodulation         : 3.54
% 24.73/14.66  BG Simplification    : 0.26
% 24.73/14.66  Subsumption          : 5.67
% 24.73/14.66  Abstraction          : 0.42
% 24.73/14.66  MUC search           : 0.00
% 24.73/14.66  Cooper               : 0.00
% 24.73/14.66  Total                : 13.91
% 24.73/14.66  Index Insertion      : 0.00
% 24.73/14.66  Index Deletion       : 0.00
% 24.73/14.66  Index Matching       : 0.00
% 24.73/14.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
