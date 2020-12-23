%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 767 expanded)
%              Number of leaves         :   40 ( 301 expanded)
%              Depth                    :   19
%              Number of atoms          :  603 (6202 expanded)
%              Number of equality atoms :   41 ( 291 expanded)
%              Maximal formula depth    :   30 (   5 average)
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

tff(f_334,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_94,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_167,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_121,axiom,(
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

tff(f_276,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_207,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_38,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_89,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_40,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_98,plain,(
    ! [B_668,A_669] :
      ( l1_pre_topc(B_668)
      | ~ m1_pre_topc(B_668,A_669)
      | ~ l1_pre_topc(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_98])).

tff(c_111,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_104])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [C_682,A_683,B_684] :
      ( m1_subset_1(C_682,k1_zfmisc_1(u1_struct_0(A_683)))
      | ~ m1_subset_1(C_682,k1_zfmisc_1(u1_struct_0(B_684)))
      | ~ m1_pre_topc(B_684,A_683)
      | ~ l1_pre_topc(A_683) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_220,plain,(
    ! [A_688,A_689,B_690] :
      ( m1_subset_1(A_688,k1_zfmisc_1(u1_struct_0(A_689)))
      | ~ m1_pre_topc(B_690,A_689)
      | ~ l1_pre_topc(A_689)
      | ~ r1_tarski(A_688,u1_struct_0(B_690)) ) ),
    inference(resolution,[status(thm)],[c_10,c_199])).

tff(c_224,plain,(
    ! [A_688] :
      ( m1_subset_1(A_688,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_688,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_220])).

tff(c_232,plain,(
    ! [A_688] :
      ( m1_subset_1(A_688,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_688,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_224])).

tff(c_607,plain,(
    ! [D_723,C_724,A_725] :
      ( v3_pre_topc(D_723,C_724)
      | ~ m1_subset_1(D_723,k1_zfmisc_1(u1_struct_0(C_724)))
      | ~ v3_pre_topc(D_723,A_725)
      | ~ m1_pre_topc(C_724,A_725)
      | ~ m1_subset_1(D_723,k1_zfmisc_1(u1_struct_0(A_725)))
      | ~ l1_pre_topc(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1997,plain,(
    ! [A_806,C_807,A_808] :
      ( v3_pre_topc(A_806,C_807)
      | ~ v3_pre_topc(A_806,A_808)
      | ~ m1_pre_topc(C_807,A_808)
      | ~ m1_subset_1(A_806,k1_zfmisc_1(u1_struct_0(A_808)))
      | ~ l1_pre_topc(A_808)
      | ~ r1_tarski(A_806,u1_struct_0(C_807)) ) ),
    inference(resolution,[status(thm)],[c_10,c_607])).

tff(c_2005,plain,(
    ! [A_806] :
      ( v3_pre_topc(A_806,'#skF_3')
      | ~ v3_pre_topc(A_806,'#skF_4')
      | ~ m1_subset_1(A_806,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_806,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1997])).

tff(c_2026,plain,(
    ! [A_809] :
      ( v3_pre_topc(A_809,'#skF_3')
      | ~ v3_pre_topc(A_809,'#skF_4')
      | ~ m1_subset_1(A_809,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_809,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_2005])).

tff(c_2064,plain,(
    ! [A_810] :
      ( v3_pre_topc(A_810,'#skF_3')
      | ~ v3_pre_topc(A_810,'#skF_4')
      | ~ r1_tarski(A_810,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_232,c_2026])).

tff(c_2132,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2064])).

tff(c_2134,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2132])).

tff(c_239,plain,(
    ! [A_691] :
      ( m1_subset_1(A_691,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_691,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_224])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_247,plain,(
    ! [A_692] :
      ( r1_tarski(A_692,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_692,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_239,c_8])).

tff(c_262,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_247])).

tff(c_44,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_2007,plain,(
    ! [A_806] :
      ( v3_pre_topc(A_806,'#skF_4')
      | ~ v3_pre_topc(A_806,'#skF_2')
      | ~ m1_subset_1(A_806,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_806,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_1997])).

tff(c_2156,plain,(
    ! [A_818] :
      ( v3_pre_topc(A_818,'#skF_4')
      | ~ v3_pre_topc(A_818,'#skF_2')
      | ~ m1_subset_1(A_818,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_818,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2007])).

tff(c_2185,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_2156])).

tff(c_2204,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_44,c_2185])).

tff(c_2206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2134,c_2204])).

tff(c_2208,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2132])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_90,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_148,plain,(
    ! [B_674,A_675] :
      ( v2_pre_topc(B_674)
      | ~ m1_pre_topc(B_674,A_675)
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_154,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_163,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_154])).

tff(c_307,plain,(
    ! [B_700,C_701,A_702] :
      ( r1_tarski(u1_struct_0(B_700),u1_struct_0(C_701))
      | ~ m1_pre_topc(B_700,C_701)
      | ~ m1_pre_topc(C_701,A_702)
      | ~ m1_pre_topc(B_700,A_702)
      | ~ l1_pre_topc(A_702)
      | ~ v2_pre_topc(A_702) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_311,plain,(
    ! [B_700] :
      ( r1_tarski(u1_struct_0(B_700),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_700,'#skF_3')
      | ~ m1_pre_topc(B_700,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_307])).

tff(c_339,plain,(
    ! [B_706] :
      ( r1_tarski(u1_struct_0(B_706),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_706,'#skF_3')
      | ~ m1_pre_topc(B_706,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_111,c_311])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_280,plain,
    ( u1_struct_0('#skF_3') = u1_struct_0('#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_263,c_2])).

tff(c_330,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_348,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_339,c_330])).

tff(c_351,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_366,plain,(
    ! [B_708,C_709,A_710] :
      ( m1_pre_topc(B_708,C_709)
      | ~ r1_tarski(u1_struct_0(B_708),u1_struct_0(C_709))
      | ~ m1_pre_topc(C_709,A_710)
      | ~ m1_pre_topc(B_708,A_710)
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_392,plain,(
    ! [B_711,A_712] :
      ( m1_pre_topc(B_711,B_711)
      | ~ m1_pre_topc(B_711,A_712)
      | ~ l1_pre_topc(A_712)
      | ~ v2_pre_topc(A_712) ) ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_398,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_392])).

tff(c_407,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_398])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_407])).

tff(c_411,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_16,plain,(
    ! [C_17,A_11,B_15] :
      ( m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(B_15)))
      | ~ m1_pre_topc(B_15,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [A_691,A_11] :
      ( m1_subset_1(A_691,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc('#skF_4',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ r1_tarski(A_691,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_239,c_16])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_87,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_86])).

tff(c_169,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_88,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_197,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_88])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_1039,plain,(
    ! [E_750,A_751,D_752,C_754,B_753] :
      ( k3_tmap_1(A_751,B_753,C_754,D_752,E_750) = k2_partfun1(u1_struct_0(C_754),u1_struct_0(B_753),E_750,u1_struct_0(D_752))
      | ~ m1_pre_topc(D_752,C_754)
      | ~ m1_subset_1(E_750,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_754),u1_struct_0(B_753))))
      | ~ v1_funct_2(E_750,u1_struct_0(C_754),u1_struct_0(B_753))
      | ~ v1_funct_1(E_750)
      | ~ m1_pre_topc(D_752,A_751)
      | ~ m1_pre_topc(C_754,A_751)
      | ~ l1_pre_topc(B_753)
      | ~ v2_pre_topc(B_753)
      | v2_struct_0(B_753)
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1041,plain,(
    ! [A_751,D_752] :
      ( k3_tmap_1(A_751,'#skF_1','#skF_4',D_752,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_752))
      | ~ m1_pre_topc(D_752,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_752,A_751)
      | ~ m1_pre_topc('#skF_4',A_751)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(resolution,[status(thm)],[c_54,c_1039])).

tff(c_1047,plain,(
    ! [A_751,D_752] :
      ( k3_tmap_1(A_751,'#skF_1','#skF_4',D_752,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_752))
      | ~ m1_pre_topc(D_752,'#skF_4')
      | ~ m1_pre_topc(D_752,A_751)
      | ~ m1_pre_topc('#skF_4',A_751)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_1041])).

tff(c_1140,plain,(
    ! [A_759,D_760] :
      ( k3_tmap_1(A_759,'#skF_1','#skF_4',D_760,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_760))
      | ~ m1_pre_topc(D_760,'#skF_4')
      | ~ m1_pre_topc(D_760,A_759)
      | ~ m1_pre_topc('#skF_4',A_759)
      | ~ l1_pre_topc(A_759)
      | ~ v2_pre_topc(A_759)
      | v2_struct_0(A_759) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1047])).

tff(c_1152,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1140])).

tff(c_1174,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_52,c_1152])).

tff(c_1175,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1174])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_334])).

tff(c_818,plain,(
    ! [A_732,B_733,C_734,D_735] :
      ( k2_partfun1(u1_struct_0(A_732),u1_struct_0(B_733),C_734,u1_struct_0(D_735)) = k2_tmap_1(A_732,B_733,C_734,D_735)
      | ~ m1_pre_topc(D_735,A_732)
      | ~ m1_subset_1(C_734,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_732),u1_struct_0(B_733))))
      | ~ v1_funct_2(C_734,u1_struct_0(A_732),u1_struct_0(B_733))
      | ~ v1_funct_1(C_734)
      | ~ l1_pre_topc(B_733)
      | ~ v2_pre_topc(B_733)
      | v2_struct_0(B_733)
      | ~ l1_pre_topc(A_732)
      | ~ v2_pre_topc(A_732)
      | v2_struct_0(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_820,plain,(
    ! [D_735] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_735)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_735)
      | ~ m1_pre_topc(D_735,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_818])).

tff(c_826,plain,(
    ! [D_735] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_735)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_735)
      | ~ m1_pre_topc(D_735,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_111,c_76,c_74,c_58,c_56,c_820])).

tff(c_827,plain,(
    ! [D_735] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_735)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_735)
      | ~ m1_pre_topc(D_735,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78,c_826])).

tff(c_1179,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_827])).

tff(c_1186,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1179])).

tff(c_1191,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_169])).

tff(c_1436,plain,(
    ! [F_782,H_776,E_779,B_778,D_777,C_781,A_780] :
      ( r1_tmap_1(D_777,B_778,E_779,H_776)
      | ~ r1_tmap_1(C_781,B_778,k3_tmap_1(A_780,B_778,D_777,C_781,E_779),H_776)
      | ~ r1_tarski(F_782,u1_struct_0(C_781))
      | ~ r2_hidden(H_776,F_782)
      | ~ v3_pre_topc(F_782,D_777)
      | ~ m1_subset_1(H_776,u1_struct_0(C_781))
      | ~ m1_subset_1(H_776,u1_struct_0(D_777))
      | ~ m1_subset_1(F_782,k1_zfmisc_1(u1_struct_0(D_777)))
      | ~ m1_pre_topc(C_781,D_777)
      | ~ m1_subset_1(E_779,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_777),u1_struct_0(B_778))))
      | ~ v1_funct_2(E_779,u1_struct_0(D_777),u1_struct_0(B_778))
      | ~ v1_funct_1(E_779)
      | ~ m1_pre_topc(D_777,A_780)
      | v2_struct_0(D_777)
      | ~ m1_pre_topc(C_781,A_780)
      | v2_struct_0(C_781)
      | ~ l1_pre_topc(B_778)
      | ~ v2_pre_topc(B_778)
      | v2_struct_0(B_778)
      | ~ l1_pre_topc(A_780)
      | ~ v2_pre_topc(A_780)
      | v2_struct_0(A_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_1440,plain,(
    ! [H_776,F_782] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_776)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_776)
      | ~ r1_tarski(F_782,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_776,F_782)
      | ~ v3_pre_topc(F_782,'#skF_4')
      | ~ m1_subset_1(H_776,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_776,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_782,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_1436])).

tff(c_1445,plain,(
    ! [H_776,F_782] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_776)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_776)
      | ~ r1_tarski(F_782,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_776,F_782)
      | ~ v3_pre_topc(F_782,'#skF_4')
      | ~ m1_subset_1(H_776,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_776,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_782,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_76,c_74,c_64,c_60,c_58,c_56,c_54,c_52,c_1440])).

tff(c_2399,plain,(
    ! [H_835,F_836] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_835)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_835)
      | ~ r1_tarski(F_836,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_835,F_836)
      | ~ v3_pre_topc(F_836,'#skF_4')
      | ~ m1_subset_1(H_835,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_835,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_836,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_78,c_66,c_62,c_1445])).

tff(c_2404,plain,(
    ! [F_836] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_836,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_836)
      | ~ v3_pre_topc(F_836,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_836,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1191,c_2399])).

tff(c_2411,plain,(
    ! [F_836] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_836,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_836)
      | ~ v3_pre_topc(F_836,'#skF_4')
      | ~ m1_subset_1(F_836,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_46,c_2404])).

tff(c_2545,plain,(
    ! [F_845] :
      ( ~ r1_tarski(F_845,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_845)
      | ~ v3_pre_topc(F_845,'#skF_4')
      | ~ m1_subset_1(F_845,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_2411])).

tff(c_2549,plain,(
    ! [A_691] :
      ( ~ r2_hidden('#skF_8',A_691)
      | ~ v3_pre_topc(A_691,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_691,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_245,c_2545])).

tff(c_2583,plain,(
    ! [A_846] :
      ( ~ r2_hidden('#skF_8',A_846)
      | ~ v3_pre_topc(A_846,'#skF_4')
      | ~ r1_tarski(A_846,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_411,c_2549])).

tff(c_2621,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2583])).

tff(c_2654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_90,c_2621])).

tff(c_2655,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_3781,plain,(
    ! [D_936,B_933,A_932,C_935,F_934] :
      ( r1_tmap_1(D_936,A_932,k2_tmap_1(B_933,A_932,C_935,D_936),F_934)
      | ~ r1_tmap_1(B_933,A_932,C_935,F_934)
      | ~ m1_subset_1(F_934,u1_struct_0(D_936))
      | ~ m1_subset_1(F_934,u1_struct_0(B_933))
      | ~ m1_pre_topc(D_936,B_933)
      | v2_struct_0(D_936)
      | ~ m1_subset_1(C_935,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_933),u1_struct_0(A_932))))
      | ~ v1_funct_2(C_935,u1_struct_0(B_933),u1_struct_0(A_932))
      | ~ v1_funct_1(C_935)
      | ~ l1_pre_topc(B_933)
      | ~ v2_pre_topc(B_933)
      | v2_struct_0(B_933)
      | ~ l1_pre_topc(A_932)
      | ~ v2_pre_topc(A_932)
      | v2_struct_0(A_932) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_3783,plain,(
    ! [D_936,F_934] :
      ( r1_tmap_1(D_936,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_936),F_934)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_934)
      | ~ m1_subset_1(F_934,u1_struct_0(D_936))
      | ~ m1_subset_1(F_934,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_936,'#skF_4')
      | v2_struct_0(D_936)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_3781])).

tff(c_3789,plain,(
    ! [D_936,F_934] :
      ( r1_tmap_1(D_936,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_936),F_934)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_934)
      | ~ m1_subset_1(F_934,u1_struct_0(D_936))
      | ~ m1_subset_1(F_934,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_936,'#skF_4')
      | v2_struct_0(D_936)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_163,c_111,c_58,c_56,c_3783])).

tff(c_4063,plain,(
    ! [D_949,F_950] :
      ( r1_tmap_1(D_949,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_949),F_950)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_950)
      | ~ m1_subset_1(F_950,u1_struct_0(D_949))
      | ~ m1_subset_1(F_950,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_949,'#skF_4')
      | v2_struct_0(D_949) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_3789])).

tff(c_2819,plain,(
    ! [B_874,C_875,A_876] :
      ( m1_pre_topc(B_874,C_875)
      | ~ r1_tarski(u1_struct_0(B_874),u1_struct_0(C_875))
      | ~ m1_pre_topc(C_875,A_876)
      | ~ m1_pre_topc(B_874,A_876)
      | ~ l1_pre_topc(A_876)
      | ~ v2_pre_topc(A_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2836,plain,(
    ! [B_877,A_878] :
      ( m1_pre_topc(B_877,B_877)
      | ~ m1_pre_topc(B_877,A_878)
      | ~ l1_pre_topc(A_878)
      | ~ v2_pre_topc(A_878) ) ),
    inference(resolution,[status(thm)],[c_6,c_2819])).

tff(c_2842,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2836])).

tff(c_2851,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2842])).

tff(c_3559,plain,(
    ! [B_921,D_920,E_918,A_919,C_922] :
      ( k3_tmap_1(A_919,B_921,C_922,D_920,E_918) = k2_partfun1(u1_struct_0(C_922),u1_struct_0(B_921),E_918,u1_struct_0(D_920))
      | ~ m1_pre_topc(D_920,C_922)
      | ~ m1_subset_1(E_918,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_922),u1_struct_0(B_921))))
      | ~ v1_funct_2(E_918,u1_struct_0(C_922),u1_struct_0(B_921))
      | ~ v1_funct_1(E_918)
      | ~ m1_pre_topc(D_920,A_919)
      | ~ m1_pre_topc(C_922,A_919)
      | ~ l1_pre_topc(B_921)
      | ~ v2_pre_topc(B_921)
      | v2_struct_0(B_921)
      | ~ l1_pre_topc(A_919)
      | ~ v2_pre_topc(A_919)
      | v2_struct_0(A_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3561,plain,(
    ! [A_919,D_920] :
      ( k3_tmap_1(A_919,'#skF_1','#skF_4',D_920,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_920))
      | ~ m1_pre_topc(D_920,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_920,A_919)
      | ~ m1_pre_topc('#skF_4',A_919)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_919)
      | ~ v2_pre_topc(A_919)
      | v2_struct_0(A_919) ) ),
    inference(resolution,[status(thm)],[c_54,c_3559])).

tff(c_3567,plain,(
    ! [A_919,D_920] :
      ( k3_tmap_1(A_919,'#skF_1','#skF_4',D_920,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_920))
      | ~ m1_pre_topc(D_920,'#skF_4')
      | ~ m1_pre_topc(D_920,A_919)
      | ~ m1_pre_topc('#skF_4',A_919)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_919)
      | ~ v2_pre_topc(A_919)
      | v2_struct_0(A_919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_3561])).

tff(c_3650,plain,(
    ! [A_928,D_929] :
      ( k3_tmap_1(A_928,'#skF_1','#skF_4',D_929,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_929))
      | ~ m1_pre_topc(D_929,'#skF_4')
      | ~ m1_pre_topc(D_929,A_928)
      | ~ m1_pre_topc('#skF_4',A_928)
      | ~ l1_pre_topc(A_928)
      | ~ v2_pre_topc(A_928)
      | v2_struct_0(A_928) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3567])).

tff(c_3658,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_3650])).

tff(c_3676,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_111,c_2851,c_52,c_3658])).

tff(c_3677,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3676])).

tff(c_3315,plain,(
    ! [A_901,B_902,C_903,D_904] :
      ( k2_partfun1(u1_struct_0(A_901),u1_struct_0(B_902),C_903,u1_struct_0(D_904)) = k2_tmap_1(A_901,B_902,C_903,D_904)
      | ~ m1_pre_topc(D_904,A_901)
      | ~ m1_subset_1(C_903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_901),u1_struct_0(B_902))))
      | ~ v1_funct_2(C_903,u1_struct_0(A_901),u1_struct_0(B_902))
      | ~ v1_funct_1(C_903)
      | ~ l1_pre_topc(B_902)
      | ~ v2_pre_topc(B_902)
      | v2_struct_0(B_902)
      | ~ l1_pre_topc(A_901)
      | ~ v2_pre_topc(A_901)
      | v2_struct_0(A_901) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3317,plain,(
    ! [D_904] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_904)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_904)
      | ~ m1_pre_topc(D_904,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_3315])).

tff(c_3323,plain,(
    ! [D_904] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_904)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_904)
      | ~ m1_pre_topc(D_904,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_111,c_76,c_74,c_58,c_56,c_3317])).

tff(c_3324,plain,(
    ! [D_904] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_904)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_904)
      | ~ m1_pre_topc(D_904,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78,c_3323])).

tff(c_3748,plain,
    ( k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3677,c_3324])).

tff(c_3755,plain,(
    k3_tmap_1('#skF_4','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3748])).

tff(c_3759,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3755,c_3677])).

tff(c_3662,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3650])).

tff(c_3684,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_52,c_3662])).

tff(c_3685,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3684])).

tff(c_3812,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3759,c_3685])).

tff(c_2656,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_3813,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_2656])).

tff(c_4066,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4063,c_3813])).

tff(c_4069,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_89,c_46,c_2655,c_4066])).

tff(c_4071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.20  
% 6.09/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.09/2.20  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.09/2.20  
% 6.09/2.20  %Foreground sorts:
% 6.09/2.20  
% 6.09/2.20  
% 6.09/2.20  %Background operators:
% 6.09/2.20  
% 6.09/2.20  
% 6.09/2.20  %Foreground operators:
% 6.09/2.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.09/2.20  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.09/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.09/2.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.09/2.20  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.09/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.09/2.20  tff('#skF_7', type, '#skF_7': $i).
% 6.09/2.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.09/2.20  tff('#skF_5', type, '#skF_5': $i).
% 6.09/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.09/2.20  tff('#skF_6', type, '#skF_6': $i).
% 6.09/2.20  tff('#skF_2', type, '#skF_2': $i).
% 6.09/2.20  tff('#skF_3', type, '#skF_3': $i).
% 6.09/2.20  tff('#skF_1', type, '#skF_1': $i).
% 6.09/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.20  tff('#skF_8', type, '#skF_8': $i).
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.09/2.20  tff('#skF_4', type, '#skF_4': $i).
% 6.09/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.09/2.20  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.09/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.09/2.20  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.09/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.09/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.20  
% 6.43/2.24  tff(f_334, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 6.43/2.24  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.43/2.24  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.43/2.24  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 6.43/2.24  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 6.43/2.24  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.43/2.24  tff(f_167, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.43/2.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.43/2.24  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 6.43/2.24  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.43/2.24  tff(f_276, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 6.43/2.24  tff(f_207, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 6.43/2.24  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_38, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_89, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 6.43/2.24  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_40, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.24  tff(c_98, plain, (![B_668, A_669]: (l1_pre_topc(B_668) | ~m1_pre_topc(B_668, A_669) | ~l1_pre_topc(A_669))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.43/2.24  tff(c_104, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_98])).
% 6.43/2.24  tff(c_111, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_104])).
% 6.43/2.24  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.43/2.24  tff(c_199, plain, (![C_682, A_683, B_684]: (m1_subset_1(C_682, k1_zfmisc_1(u1_struct_0(A_683))) | ~m1_subset_1(C_682, k1_zfmisc_1(u1_struct_0(B_684))) | ~m1_pre_topc(B_684, A_683) | ~l1_pre_topc(A_683))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.43/2.24  tff(c_220, plain, (![A_688, A_689, B_690]: (m1_subset_1(A_688, k1_zfmisc_1(u1_struct_0(A_689))) | ~m1_pre_topc(B_690, A_689) | ~l1_pre_topc(A_689) | ~r1_tarski(A_688, u1_struct_0(B_690)))), inference(resolution, [status(thm)], [c_10, c_199])).
% 6.43/2.24  tff(c_224, plain, (![A_688]: (m1_subset_1(A_688, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_688, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_220])).
% 6.43/2.24  tff(c_232, plain, (![A_688]: (m1_subset_1(A_688, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_688, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_224])).
% 6.43/2.25  tff(c_607, plain, (![D_723, C_724, A_725]: (v3_pre_topc(D_723, C_724) | ~m1_subset_1(D_723, k1_zfmisc_1(u1_struct_0(C_724))) | ~v3_pre_topc(D_723, A_725) | ~m1_pre_topc(C_724, A_725) | ~m1_subset_1(D_723, k1_zfmisc_1(u1_struct_0(A_725))) | ~l1_pre_topc(A_725))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.43/2.25  tff(c_1997, plain, (![A_806, C_807, A_808]: (v3_pre_topc(A_806, C_807) | ~v3_pre_topc(A_806, A_808) | ~m1_pre_topc(C_807, A_808) | ~m1_subset_1(A_806, k1_zfmisc_1(u1_struct_0(A_808))) | ~l1_pre_topc(A_808) | ~r1_tarski(A_806, u1_struct_0(C_807)))), inference(resolution, [status(thm)], [c_10, c_607])).
% 6.43/2.25  tff(c_2005, plain, (![A_806]: (v3_pre_topc(A_806, '#skF_3') | ~v3_pre_topc(A_806, '#skF_4') | ~m1_subset_1(A_806, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_806, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_1997])).
% 6.43/2.25  tff(c_2026, plain, (![A_809]: (v3_pre_topc(A_809, '#skF_3') | ~v3_pre_topc(A_809, '#skF_4') | ~m1_subset_1(A_809, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_809, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_2005])).
% 6.43/2.25  tff(c_2064, plain, (![A_810]: (v3_pre_topc(A_810, '#skF_3') | ~v3_pre_topc(A_810, '#skF_4') | ~r1_tarski(A_810, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_232, c_2026])).
% 6.43/2.25  tff(c_2132, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_2064])).
% 6.43/2.25  tff(c_2134, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2132])).
% 6.43/2.25  tff(c_239, plain, (![A_691]: (m1_subset_1(A_691, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_691, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_224])).
% 6.43/2.25  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.43/2.25  tff(c_247, plain, (![A_692]: (r1_tarski(A_692, u1_struct_0('#skF_4')) | ~r1_tarski(A_692, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_239, c_8])).
% 6.43/2.25  tff(c_262, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_247])).
% 6.43/2.25  tff(c_44, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_2007, plain, (![A_806]: (v3_pre_topc(A_806, '#skF_4') | ~v3_pre_topc(A_806, '#skF_2') | ~m1_subset_1(A_806, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_806, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_1997])).
% 6.43/2.25  tff(c_2156, plain, (![A_818]: (v3_pre_topc(A_818, '#skF_4') | ~v3_pre_topc(A_818, '#skF_2') | ~m1_subset_1(A_818, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_818, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2007])).
% 6.43/2.25  tff(c_2185, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_2156])).
% 6.43/2.25  tff(c_2204, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_44, c_2185])).
% 6.43/2.25  tff(c_2206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2134, c_2204])).
% 6.43/2.25  tff(c_2208, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_2132])).
% 6.43/2.25  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_90, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 6.43/2.25  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_148, plain, (![B_674, A_675]: (v2_pre_topc(B_674) | ~m1_pre_topc(B_674, A_675) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.43/2.25  tff(c_154, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_148])).
% 6.43/2.25  tff(c_163, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_154])).
% 6.43/2.25  tff(c_307, plain, (![B_700, C_701, A_702]: (r1_tarski(u1_struct_0(B_700), u1_struct_0(C_701)) | ~m1_pre_topc(B_700, C_701) | ~m1_pre_topc(C_701, A_702) | ~m1_pre_topc(B_700, A_702) | ~l1_pre_topc(A_702) | ~v2_pre_topc(A_702))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.43/2.25  tff(c_311, plain, (![B_700]: (r1_tarski(u1_struct_0(B_700), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_700, '#skF_3') | ~m1_pre_topc(B_700, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_307])).
% 6.43/2.25  tff(c_339, plain, (![B_706]: (r1_tarski(u1_struct_0(B_706), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_706, '#skF_3') | ~m1_pre_topc(B_706, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_111, c_311])).
% 6.43/2.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.43/2.25  tff(c_263, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_247])).
% 6.43/2.25  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.43/2.25  tff(c_280, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_263, c_2])).
% 6.43/2.25  tff(c_330, plain, (~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_280])).
% 6.43/2.25  tff(c_348, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_339, c_330])).
% 6.43/2.25  tff(c_351, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_348])).
% 6.43/2.25  tff(c_366, plain, (![B_708, C_709, A_710]: (m1_pre_topc(B_708, C_709) | ~r1_tarski(u1_struct_0(B_708), u1_struct_0(C_709)) | ~m1_pre_topc(C_709, A_710) | ~m1_pre_topc(B_708, A_710) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.43/2.25  tff(c_392, plain, (![B_711, A_712]: (m1_pre_topc(B_711, B_711) | ~m1_pre_topc(B_711, A_712) | ~l1_pre_topc(A_712) | ~v2_pre_topc(A_712))), inference(resolution, [status(thm)], [c_6, c_366])).
% 6.43/2.25  tff(c_398, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_392])).
% 6.43/2.25  tff(c_407, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_398])).
% 6.43/2.25  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_407])).
% 6.43/2.25  tff(c_411, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_348])).
% 6.43/2.25  tff(c_16, plain, (![C_17, A_11, B_15]: (m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(B_15))) | ~m1_pre_topc(B_15, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.43/2.25  tff(c_245, plain, (![A_691, A_11]: (m1_subset_1(A_691, k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc('#skF_4', A_11) | ~l1_pre_topc(A_11) | ~r1_tarski(A_691, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_239, c_16])).
% 6.43/2.25  tff(c_86, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_87, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_86])).
% 6.43/2.25  tff(c_169, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 6.43/2.25  tff(c_80, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_88, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 6.43/2.25  tff(c_197, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_88])).
% 6.43/2.25  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_1039, plain, (![E_750, A_751, D_752, C_754, B_753]: (k3_tmap_1(A_751, B_753, C_754, D_752, E_750)=k2_partfun1(u1_struct_0(C_754), u1_struct_0(B_753), E_750, u1_struct_0(D_752)) | ~m1_pre_topc(D_752, C_754) | ~m1_subset_1(E_750, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_754), u1_struct_0(B_753)))) | ~v1_funct_2(E_750, u1_struct_0(C_754), u1_struct_0(B_753)) | ~v1_funct_1(E_750) | ~m1_pre_topc(D_752, A_751) | ~m1_pre_topc(C_754, A_751) | ~l1_pre_topc(B_753) | ~v2_pre_topc(B_753) | v2_struct_0(B_753) | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.43/2.25  tff(c_1041, plain, (![A_751, D_752]: (k3_tmap_1(A_751, '#skF_1', '#skF_4', D_752, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_752)) | ~m1_pre_topc(D_752, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_752, A_751) | ~m1_pre_topc('#skF_4', A_751) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(resolution, [status(thm)], [c_54, c_1039])).
% 6.43/2.25  tff(c_1047, plain, (![A_751, D_752]: (k3_tmap_1(A_751, '#skF_1', '#skF_4', D_752, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_752)) | ~m1_pre_topc(D_752, '#skF_4') | ~m1_pre_topc(D_752, A_751) | ~m1_pre_topc('#skF_4', A_751) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_1041])).
% 6.43/2.25  tff(c_1140, plain, (![A_759, D_760]: (k3_tmap_1(A_759, '#skF_1', '#skF_4', D_760, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_760)) | ~m1_pre_topc(D_760, '#skF_4') | ~m1_pre_topc(D_760, A_759) | ~m1_pre_topc('#skF_4', A_759) | ~l1_pre_topc(A_759) | ~v2_pre_topc(A_759) | v2_struct_0(A_759))), inference(negUnitSimplification, [status(thm)], [c_78, c_1047])).
% 6.43/2.25  tff(c_1152, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1140])).
% 6.43/2.25  tff(c_1174, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_52, c_1152])).
% 6.43/2.25  tff(c_1175, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_1174])).
% 6.43/2.25  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_334])).
% 6.43/2.25  tff(c_818, plain, (![A_732, B_733, C_734, D_735]: (k2_partfun1(u1_struct_0(A_732), u1_struct_0(B_733), C_734, u1_struct_0(D_735))=k2_tmap_1(A_732, B_733, C_734, D_735) | ~m1_pre_topc(D_735, A_732) | ~m1_subset_1(C_734, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_732), u1_struct_0(B_733)))) | ~v1_funct_2(C_734, u1_struct_0(A_732), u1_struct_0(B_733)) | ~v1_funct_1(C_734) | ~l1_pre_topc(B_733) | ~v2_pre_topc(B_733) | v2_struct_0(B_733) | ~l1_pre_topc(A_732) | ~v2_pre_topc(A_732) | v2_struct_0(A_732))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.43/2.25  tff(c_820, plain, (![D_735]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_735))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_735) | ~m1_pre_topc(D_735, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_818])).
% 6.43/2.25  tff(c_826, plain, (![D_735]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_735))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_735) | ~m1_pre_topc(D_735, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_111, c_76, c_74, c_58, c_56, c_820])).
% 6.43/2.25  tff(c_827, plain, (![D_735]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_735))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_735) | ~m1_pre_topc(D_735, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_78, c_826])).
% 6.43/2.25  tff(c_1179, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1175, c_827])).
% 6.43/2.25  tff(c_1186, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1179])).
% 6.43/2.25  tff(c_1191, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_169])).
% 6.43/2.25  tff(c_1436, plain, (![F_782, H_776, E_779, B_778, D_777, C_781, A_780]: (r1_tmap_1(D_777, B_778, E_779, H_776) | ~r1_tmap_1(C_781, B_778, k3_tmap_1(A_780, B_778, D_777, C_781, E_779), H_776) | ~r1_tarski(F_782, u1_struct_0(C_781)) | ~r2_hidden(H_776, F_782) | ~v3_pre_topc(F_782, D_777) | ~m1_subset_1(H_776, u1_struct_0(C_781)) | ~m1_subset_1(H_776, u1_struct_0(D_777)) | ~m1_subset_1(F_782, k1_zfmisc_1(u1_struct_0(D_777))) | ~m1_pre_topc(C_781, D_777) | ~m1_subset_1(E_779, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_777), u1_struct_0(B_778)))) | ~v1_funct_2(E_779, u1_struct_0(D_777), u1_struct_0(B_778)) | ~v1_funct_1(E_779) | ~m1_pre_topc(D_777, A_780) | v2_struct_0(D_777) | ~m1_pre_topc(C_781, A_780) | v2_struct_0(C_781) | ~l1_pre_topc(B_778) | ~v2_pre_topc(B_778) | v2_struct_0(B_778) | ~l1_pre_topc(A_780) | ~v2_pre_topc(A_780) | v2_struct_0(A_780))), inference(cnfTransformation, [status(thm)], [f_276])).
% 6.43/2.25  tff(c_1440, plain, (![H_776, F_782]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_776) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_776) | ~r1_tarski(F_782, u1_struct_0('#skF_3')) | ~r2_hidden(H_776, F_782) | ~v3_pre_topc(F_782, '#skF_4') | ~m1_subset_1(H_776, u1_struct_0('#skF_3')) | ~m1_subset_1(H_776, u1_struct_0('#skF_4')) | ~m1_subset_1(F_782, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_1436])).
% 6.43/2.25  tff(c_1445, plain, (![H_776, F_782]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_776) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_776) | ~r1_tarski(F_782, u1_struct_0('#skF_3')) | ~r2_hidden(H_776, F_782) | ~v3_pre_topc(F_782, '#skF_4') | ~m1_subset_1(H_776, u1_struct_0('#skF_3')) | ~m1_subset_1(H_776, u1_struct_0('#skF_4')) | ~m1_subset_1(F_782, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_76, c_74, c_64, c_60, c_58, c_56, c_54, c_52, c_1440])).
% 6.43/2.25  tff(c_2399, plain, (![H_835, F_836]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_835) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_835) | ~r1_tarski(F_836, u1_struct_0('#skF_3')) | ~r2_hidden(H_835, F_836) | ~v3_pre_topc(F_836, '#skF_4') | ~m1_subset_1(H_835, u1_struct_0('#skF_3')) | ~m1_subset_1(H_835, u1_struct_0('#skF_4')) | ~m1_subset_1(F_836, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_78, c_66, c_62, c_1445])).
% 6.43/2.25  tff(c_2404, plain, (![F_836]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_836, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_836) | ~v3_pre_topc(F_836, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_836, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1191, c_2399])).
% 6.43/2.25  tff(c_2411, plain, (![F_836]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_836, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_836) | ~v3_pre_topc(F_836, '#skF_4') | ~m1_subset_1(F_836, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_46, c_2404])).
% 6.43/2.25  tff(c_2545, plain, (![F_845]: (~r1_tarski(F_845, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_845) | ~v3_pre_topc(F_845, '#skF_4') | ~m1_subset_1(F_845, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_197, c_2411])).
% 6.43/2.25  tff(c_2549, plain, (![A_691]: (~r2_hidden('#skF_8', A_691) | ~v3_pre_topc(A_691, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_691, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_245, c_2545])).
% 6.43/2.25  tff(c_2583, plain, (![A_846]: (~r2_hidden('#skF_8', A_846) | ~v3_pre_topc(A_846, '#skF_4') | ~r1_tarski(A_846, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_411, c_2549])).
% 6.43/2.25  tff(c_2621, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_2583])).
% 6.43/2.25  tff(c_2654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2208, c_90, c_2621])).
% 6.43/2.25  tff(c_2655, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 6.43/2.25  tff(c_3781, plain, (![D_936, B_933, A_932, C_935, F_934]: (r1_tmap_1(D_936, A_932, k2_tmap_1(B_933, A_932, C_935, D_936), F_934) | ~r1_tmap_1(B_933, A_932, C_935, F_934) | ~m1_subset_1(F_934, u1_struct_0(D_936)) | ~m1_subset_1(F_934, u1_struct_0(B_933)) | ~m1_pre_topc(D_936, B_933) | v2_struct_0(D_936) | ~m1_subset_1(C_935, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_933), u1_struct_0(A_932)))) | ~v1_funct_2(C_935, u1_struct_0(B_933), u1_struct_0(A_932)) | ~v1_funct_1(C_935) | ~l1_pre_topc(B_933) | ~v2_pre_topc(B_933) | v2_struct_0(B_933) | ~l1_pre_topc(A_932) | ~v2_pre_topc(A_932) | v2_struct_0(A_932))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.43/2.25  tff(c_3783, plain, (![D_936, F_934]: (r1_tmap_1(D_936, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_936), F_934) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_934) | ~m1_subset_1(F_934, u1_struct_0(D_936)) | ~m1_subset_1(F_934, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_936, '#skF_4') | v2_struct_0(D_936) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_3781])).
% 6.43/2.25  tff(c_3789, plain, (![D_936, F_934]: (r1_tmap_1(D_936, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_936), F_934) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_934) | ~m1_subset_1(F_934, u1_struct_0(D_936)) | ~m1_subset_1(F_934, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_936, '#skF_4') | v2_struct_0(D_936) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_163, c_111, c_58, c_56, c_3783])).
% 6.43/2.25  tff(c_4063, plain, (![D_949, F_950]: (r1_tmap_1(D_949, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_949), F_950) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_950) | ~m1_subset_1(F_950, u1_struct_0(D_949)) | ~m1_subset_1(F_950, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_949, '#skF_4') | v2_struct_0(D_949))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_3789])).
% 6.43/2.25  tff(c_2819, plain, (![B_874, C_875, A_876]: (m1_pre_topc(B_874, C_875) | ~r1_tarski(u1_struct_0(B_874), u1_struct_0(C_875)) | ~m1_pre_topc(C_875, A_876) | ~m1_pre_topc(B_874, A_876) | ~l1_pre_topc(A_876) | ~v2_pre_topc(A_876))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.43/2.25  tff(c_2836, plain, (![B_877, A_878]: (m1_pre_topc(B_877, B_877) | ~m1_pre_topc(B_877, A_878) | ~l1_pre_topc(A_878) | ~v2_pre_topc(A_878))), inference(resolution, [status(thm)], [c_6, c_2819])).
% 6.43/2.25  tff(c_2842, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2836])).
% 6.43/2.25  tff(c_2851, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2842])).
% 6.43/2.25  tff(c_3559, plain, (![B_921, D_920, E_918, A_919, C_922]: (k3_tmap_1(A_919, B_921, C_922, D_920, E_918)=k2_partfun1(u1_struct_0(C_922), u1_struct_0(B_921), E_918, u1_struct_0(D_920)) | ~m1_pre_topc(D_920, C_922) | ~m1_subset_1(E_918, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_922), u1_struct_0(B_921)))) | ~v1_funct_2(E_918, u1_struct_0(C_922), u1_struct_0(B_921)) | ~v1_funct_1(E_918) | ~m1_pre_topc(D_920, A_919) | ~m1_pre_topc(C_922, A_919) | ~l1_pre_topc(B_921) | ~v2_pre_topc(B_921) | v2_struct_0(B_921) | ~l1_pre_topc(A_919) | ~v2_pre_topc(A_919) | v2_struct_0(A_919))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.43/2.25  tff(c_3561, plain, (![A_919, D_920]: (k3_tmap_1(A_919, '#skF_1', '#skF_4', D_920, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_920)) | ~m1_pre_topc(D_920, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_920, A_919) | ~m1_pre_topc('#skF_4', A_919) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_919) | ~v2_pre_topc(A_919) | v2_struct_0(A_919))), inference(resolution, [status(thm)], [c_54, c_3559])).
% 6.43/2.25  tff(c_3567, plain, (![A_919, D_920]: (k3_tmap_1(A_919, '#skF_1', '#skF_4', D_920, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_920)) | ~m1_pre_topc(D_920, '#skF_4') | ~m1_pre_topc(D_920, A_919) | ~m1_pre_topc('#skF_4', A_919) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_919) | ~v2_pre_topc(A_919) | v2_struct_0(A_919))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_3561])).
% 6.43/2.25  tff(c_3650, plain, (![A_928, D_929]: (k3_tmap_1(A_928, '#skF_1', '#skF_4', D_929, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_929)) | ~m1_pre_topc(D_929, '#skF_4') | ~m1_pre_topc(D_929, A_928) | ~m1_pre_topc('#skF_4', A_928) | ~l1_pre_topc(A_928) | ~v2_pre_topc(A_928) | v2_struct_0(A_928))), inference(negUnitSimplification, [status(thm)], [c_78, c_3567])).
% 6.43/2.25  tff(c_3658, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_3650])).
% 6.43/2.25  tff(c_3676, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_111, c_2851, c_52, c_3658])).
% 6.43/2.25  tff(c_3677, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_3676])).
% 6.43/2.25  tff(c_3315, plain, (![A_901, B_902, C_903, D_904]: (k2_partfun1(u1_struct_0(A_901), u1_struct_0(B_902), C_903, u1_struct_0(D_904))=k2_tmap_1(A_901, B_902, C_903, D_904) | ~m1_pre_topc(D_904, A_901) | ~m1_subset_1(C_903, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_901), u1_struct_0(B_902)))) | ~v1_funct_2(C_903, u1_struct_0(A_901), u1_struct_0(B_902)) | ~v1_funct_1(C_903) | ~l1_pre_topc(B_902) | ~v2_pre_topc(B_902) | v2_struct_0(B_902) | ~l1_pre_topc(A_901) | ~v2_pre_topc(A_901) | v2_struct_0(A_901))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.43/2.25  tff(c_3317, plain, (![D_904]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_904))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_904) | ~m1_pre_topc(D_904, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3315])).
% 6.43/2.25  tff(c_3323, plain, (![D_904]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_904))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_904) | ~m1_pre_topc(D_904, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_111, c_76, c_74, c_58, c_56, c_3317])).
% 6.43/2.25  tff(c_3324, plain, (![D_904]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_904))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_904) | ~m1_pre_topc(D_904, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_78, c_3323])).
% 6.43/2.25  tff(c_3748, plain, (k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3677, c_3324])).
% 6.43/2.25  tff(c_3755, plain, (k3_tmap_1('#skF_4', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3748])).
% 6.43/2.25  tff(c_3759, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3755, c_3677])).
% 6.43/2.25  tff(c_3662, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3650])).
% 6.43/2.25  tff(c_3684, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_52, c_3662])).
% 6.43/2.25  tff(c_3685, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_3684])).
% 6.43/2.25  tff(c_3812, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3759, c_3685])).
% 6.43/2.25  tff(c_2656, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 6.43/2.25  tff(c_3813, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3812, c_2656])).
% 6.43/2.25  tff(c_4066, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_4063, c_3813])).
% 6.43/2.25  tff(c_4069, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_89, c_46, c_2655, c_4066])).
% 6.43/2.25  tff(c_4071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4069])).
% 6.43/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.43/2.25  
% 6.43/2.25  Inference rules
% 6.43/2.25  ----------------------
% 6.43/2.25  #Ref     : 0
% 6.43/2.25  #Sup     : 761
% 6.43/2.25  #Fact    : 0
% 6.43/2.25  #Define  : 0
% 6.43/2.25  #Split   : 18
% 6.43/2.25  #Chain   : 0
% 6.43/2.25  #Close   : 0
% 6.43/2.25  
% 6.43/2.25  Ordering : KBO
% 6.43/2.25  
% 6.43/2.25  Simplification rules
% 6.43/2.25  ----------------------
% 6.43/2.25  #Subsume      : 346
% 6.43/2.25  #Demod        : 740
% 6.43/2.25  #Tautology    : 140
% 6.43/2.25  #SimpNegUnit  : 56
% 6.43/2.25  #BackRed      : 6
% 6.43/2.25  
% 6.43/2.25  #Partial instantiations: 0
% 6.43/2.25  #Strategies tried      : 1
% 6.43/2.25  
% 6.43/2.25  Timing (in seconds)
% 6.43/2.25  ----------------------
% 6.43/2.25  Preprocessing        : 0.43
% 6.43/2.25  Parsing              : 0.21
% 6.43/2.25  CNF conversion       : 0.07
% 6.43/2.25  Main loop            : 0.97
% 6.43/2.25  Inferencing          : 0.32
% 6.43/2.25  Reduction            : 0.35
% 6.43/2.25  Demodulation         : 0.25
% 6.43/2.25  BG Simplification    : 0.04
% 6.43/2.25  Subsumption          : 0.21
% 6.43/2.25  Abstraction          : 0.04
% 6.43/2.25  MUC search           : 0.00
% 6.43/2.25  Cooper               : 0.00
% 6.43/2.26  Total                : 1.48
% 6.43/2.26  Index Insertion      : 0.00
% 6.43/2.26  Index Deletion       : 0.00
% 6.43/2.26  Index Matching       : 0.00
% 6.43/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
