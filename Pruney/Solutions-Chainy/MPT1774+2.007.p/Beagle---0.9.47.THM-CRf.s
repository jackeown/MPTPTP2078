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
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 6.89s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  239 (1303 expanded)
%              Number of leaves         :   37 ( 462 expanded)
%              Depth                    :   23
%              Number of atoms          :  753 (9208 expanded)
%              Number of equality atoms :   29 ( 450 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_235,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_93,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_177,axiom,(
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
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_95,plain,(
    ! [B_566,A_567] :
      ( l1_pre_topc(B_566)
      | ~ m1_pre_topc(B_566,A_567)
      | ~ l1_pre_topc(A_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_104,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_95])).

tff(c_111,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_104])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_167,plain,(
    ! [C_576,A_577,B_578] :
      ( m1_subset_1(C_576,k1_zfmisc_1(u1_struct_0(A_577)))
      | ~ m1_subset_1(C_576,k1_zfmisc_1(u1_struct_0(B_578)))
      | ~ m1_pre_topc(B_578,A_577)
      | ~ l1_pre_topc(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_184,plain,(
    ! [A_581,A_582,B_583] :
      ( m1_subset_1(A_581,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ m1_pre_topc(B_583,A_582)
      | ~ l1_pre_topc(A_582)
      | ~ r1_tarski(A_581,u1_struct_0(B_583)) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_190,plain,(
    ! [A_581] :
      ( m1_subset_1(A_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_581,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_199,plain,(
    ! [A_581] :
      ( m1_subset_1(A_581,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_581,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_190])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_119,plain,(
    ! [B_568,A_569] :
      ( v2_pre_topc(B_568)
      | ~ m1_pre_topc(B_568,A_569)
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_137,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_128])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_14,plain,(
    ! [B_24,D_30,C_28,A_16] :
      ( k1_tops_1(B_24,D_30) = D_30
      | ~ v3_pre_topc(D_30,B_24)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0(B_24)))
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(B_24)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ! [C_597,A_598] :
      ( ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_307,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_285])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_307])).

tff(c_325,plain,(
    ! [B_599,D_600] :
      ( k1_tops_1(B_599,D_600) = D_600
      | ~ v3_pre_topc(D_600,B_599)
      | ~ m1_subset_1(D_600,k1_zfmisc_1(u1_struct_0(B_599)))
      | ~ l1_pre_topc(B_599) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_334,plain,(
    ! [A_581] :
      ( k1_tops_1('#skF_4',A_581) = A_581
      | ~ v3_pre_topc(A_581,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_581,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_199,c_325])).

tff(c_374,plain,(
    ! [A_602] :
      ( k1_tops_1('#skF_4',A_602) = A_602
      | ~ v3_pre_topc(A_602,'#skF_4')
      | ~ r1_tarski(A_602,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_334])).

tff(c_385,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_374])).

tff(c_386,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_227,plain,(
    ! [A_589] :
      ( m1_subset_1(A_589,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_589,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_190])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_238,plain,(
    ! [A_590] :
      ( r1_tarski(A_590,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_590,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_249,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_238])).

tff(c_34,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_122,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_119])).

tff(c_131,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_122])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_95])).

tff(c_107,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_98])).

tff(c_456,plain,(
    ! [B_607,A_608] :
      ( k1_tops_1(B_607,A_608) = A_608
      | ~ v3_pre_topc(A_608,B_607)
      | ~ l1_pre_topc(B_607)
      | ~ r1_tarski(A_608,u1_struct_0(B_607)) ) ),
    inference(resolution,[status(thm)],[c_4,c_325])).

tff(c_474,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_456])).

tff(c_490,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_474])).

tff(c_491,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_211,plain,(
    ! [D_585,C_586,A_587] :
      ( v3_pre_topc(D_585,C_586)
      | ~ m1_subset_1(D_585,k1_zfmisc_1(u1_struct_0(C_586)))
      | ~ v3_pre_topc(D_585,A_587)
      | ~ m1_pre_topc(C_586,A_587)
      | ~ m1_subset_1(D_585,k1_zfmisc_1(u1_struct_0(A_587)))
      | ~ l1_pre_topc(A_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1167,plain,(
    ! [A_685,C_686,A_687] :
      ( v3_pre_topc(A_685,C_686)
      | ~ v3_pre_topc(A_685,A_687)
      | ~ m1_pre_topc(C_686,A_687)
      | ~ m1_subset_1(A_685,k1_zfmisc_1(u1_struct_0(A_687)))
      | ~ l1_pre_topc(A_687)
      | ~ r1_tarski(A_685,u1_struct_0(C_686)) ) ),
    inference(resolution,[status(thm)],[c_4,c_211])).

tff(c_1171,plain,(
    ! [A_685] :
      ( v3_pre_topc(A_685,'#skF_3')
      | ~ v3_pre_topc(A_685,'#skF_2')
      | ~ m1_subset_1(A_685,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_685,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1167])).

tff(c_1186,plain,(
    ! [A_688] :
      ( v3_pre_topc(A_688,'#skF_3')
      | ~ v3_pre_topc(A_688,'#skF_2')
      | ~ m1_subset_1(A_688,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_688,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1171])).

tff(c_1215,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_1186])).

tff(c_1234,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_1215])).

tff(c_1236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_1234])).

tff(c_1237,plain,(
    k1_tops_1('#skF_3','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_1523,plain,(
    ! [C_710,A_711,B_712] :
      ( m1_connsp_2(C_710,A_711,B_712)
      | ~ r2_hidden(B_712,k1_tops_1(A_711,C_710))
      | ~ m1_subset_1(C_710,k1_zfmisc_1(u1_struct_0(A_711)))
      | ~ m1_subset_1(B_712,u1_struct_0(A_711))
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1527,plain,(
    ! [B_712] :
      ( m1_connsp_2('#skF_6','#skF_3',B_712)
      | ~ r2_hidden(B_712,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_712,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_1523])).

tff(c_1535,plain,(
    ! [B_712] :
      ( m1_connsp_2('#skF_6','#skF_3',B_712)
      | ~ r2_hidden(B_712,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_712,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_107,c_1527])).

tff(c_1536,plain,(
    ! [B_712] :
      ( m1_connsp_2('#skF_6','#skF_3',B_712)
      | ~ r2_hidden(B_712,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_712,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1535])).

tff(c_1558,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1536])).

tff(c_1573,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1558])).

tff(c_1589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1573])).

tff(c_1591,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1536])).

tff(c_10,plain,(
    ! [C_15,A_9,B_13] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_13)))
      | ~ m1_pre_topc(B_13,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1619,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_1591,c_10])).

tff(c_1957,plain,(
    ! [A_746,C_747,A_748] :
      ( v3_pre_topc(A_746,C_747)
      | ~ v3_pre_topc(A_746,A_748)
      | ~ m1_pre_topc(C_747,A_748)
      | ~ m1_subset_1(A_746,k1_zfmisc_1(u1_struct_0(A_748)))
      | ~ l1_pre_topc(A_748)
      | ~ r1_tarski(A_746,u1_struct_0(C_747)) ) ),
    inference(resolution,[status(thm)],[c_4,c_211])).

tff(c_1965,plain,(
    ! [A_746] :
      ( v3_pre_topc(A_746,'#skF_4')
      | ~ v3_pre_topc(A_746,'#skF_2')
      | ~ m1_subset_1(A_746,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_746,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1957])).

tff(c_2152,plain,(
    ! [A_760] :
      ( v3_pre_topc(A_760,'#skF_4')
      | ~ v3_pre_topc(A_760,'#skF_2')
      | ~ m1_subset_1(A_760,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_760,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1965])).

tff(c_2156,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1619,c_2152])).

tff(c_2188,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_249,c_34,c_2156])).

tff(c_2190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_2188])).

tff(c_2191,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_2737,plain,(
    ! [C_800,A_801,B_802] :
      ( m1_connsp_2(C_800,A_801,B_802)
      | ~ r2_hidden(B_802,k1_tops_1(A_801,C_800))
      | ~ m1_subset_1(C_800,k1_zfmisc_1(u1_struct_0(A_801)))
      | ~ m1_subset_1(B_802,u1_struct_0(A_801))
      | ~ l1_pre_topc(A_801)
      | ~ v2_pre_topc(A_801)
      | v2_struct_0(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2741,plain,(
    ! [B_802] :
      ( m1_connsp_2('#skF_6','#skF_4',B_802)
      | ~ r2_hidden(B_802,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_802,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2191,c_2737])).

tff(c_2749,plain,(
    ! [B_802] :
      ( m1_connsp_2('#skF_6','#skF_4',B_802)
      | ~ r2_hidden(B_802,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_802,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_111,c_2741])).

tff(c_2750,plain,(
    ! [B_802] :
      ( m1_connsp_2('#skF_6','#skF_4',B_802)
      | ~ r2_hidden(B_802,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_802,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2749])).

tff(c_2755,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2750])).

tff(c_2767,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_199,c_2755])).

tff(c_2786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2767])).

tff(c_2853,plain,(
    ! [B_807] :
      ( m1_connsp_2('#skF_6','#skF_4',B_807)
      | ~ r2_hidden(B_807,'#skF_6')
      | ~ m1_subset_1(B_807,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_2750])).

tff(c_2856,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_79,c_2853])).

tff(c_2859,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2856])).

tff(c_2788,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2750])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_118,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_166,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_77])).

tff(c_3029,plain,(
    ! [F_838,B_840,C_839,E_843,A_841,D_844,H_842] :
      ( r1_tmap_1(D_844,B_840,E_843,H_842)
      | ~ r1_tmap_1(C_839,B_840,k3_tmap_1(A_841,B_840,D_844,C_839,E_843),H_842)
      | ~ m1_connsp_2(F_838,D_844,H_842)
      | ~ r1_tarski(F_838,u1_struct_0(C_839))
      | ~ m1_subset_1(H_842,u1_struct_0(C_839))
      | ~ m1_subset_1(H_842,u1_struct_0(D_844))
      | ~ m1_subset_1(F_838,k1_zfmisc_1(u1_struct_0(D_844)))
      | ~ m1_pre_topc(C_839,D_844)
      | ~ m1_subset_1(E_843,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_844),u1_struct_0(B_840))))
      | ~ v1_funct_2(E_843,u1_struct_0(D_844),u1_struct_0(B_840))
      | ~ v1_funct_1(E_843)
      | ~ m1_pre_topc(D_844,A_841)
      | v2_struct_0(D_844)
      | ~ m1_pre_topc(C_839,A_841)
      | v2_struct_0(C_839)
      | ~ l1_pre_topc(B_840)
      | ~ v2_pre_topc(B_840)
      | v2_struct_0(B_840)
      | ~ l1_pre_topc(A_841)
      | ~ v2_pre_topc(A_841)
      | v2_struct_0(A_841) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3031,plain,(
    ! [F_838] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_838,'#skF_4','#skF_8')
      | ~ r1_tarski(F_838,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_838,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_166,c_3029])).

tff(c_3034,plain,(
    ! [F_838] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_838,'#skF_4','#skF_8')
      | ~ r1_tarski(F_838,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_838,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_54,c_50,c_48,c_46,c_44,c_42,c_79,c_36,c_3031])).

tff(c_3036,plain,(
    ! [F_845] :
      ( ~ m1_connsp_2(F_845,'#skF_4','#skF_8')
      | ~ r1_tarski(F_845,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_845,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_56,c_52,c_118,c_3034])).

tff(c_3043,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2788,c_3036])).

tff(c_3073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2859,c_3043])).

tff(c_3075,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_3076,plain,(
    ! [B_846,A_847] :
      ( v2_pre_topc(B_846)
      | ~ m1_pre_topc(B_846,A_847)
      | ~ l1_pre_topc(A_847)
      | ~ v2_pre_topc(A_847) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3079,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3076])).

tff(c_3088,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3079])).

tff(c_3256,plain,(
    ! [C_876,A_877] :
      ( ~ m1_subset_1(C_876,k1_zfmisc_1(u1_struct_0(A_877)))
      | ~ l1_pre_topc(A_877)
      | ~ v2_pre_topc(A_877) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_3278,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_3256])).

tff(c_3294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3278])).

tff(c_3296,plain,(
    ! [B_878,D_879] :
      ( k1_tops_1(B_878,D_879) = D_879
      | ~ v3_pre_topc(D_879,B_878)
      | ~ m1_subset_1(D_879,k1_zfmisc_1(u1_struct_0(B_878)))
      | ~ l1_pre_topc(B_878) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_5213,plain,(
    ! [B_1043,A_1044] :
      ( k1_tops_1(B_1043,A_1044) = A_1044
      | ~ v3_pre_topc(A_1044,B_1043)
      | ~ l1_pre_topc(B_1043)
      | ~ r1_tarski(A_1044,u1_struct_0(B_1043)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3296])).

tff(c_5234,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_5213])).

tff(c_5251,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_5234])).

tff(c_5252,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5251])).

tff(c_3108,plain,(
    ! [C_851,A_852,B_853] :
      ( m1_subset_1(C_851,k1_zfmisc_1(u1_struct_0(A_852)))
      | ~ m1_subset_1(C_851,k1_zfmisc_1(u1_struct_0(B_853)))
      | ~ m1_pre_topc(B_853,A_852)
      | ~ l1_pre_topc(A_852) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3141,plain,(
    ! [A_859,A_860,B_861] :
      ( m1_subset_1(A_859,k1_zfmisc_1(u1_struct_0(A_860)))
      | ~ m1_pre_topc(B_861,A_860)
      | ~ l1_pre_topc(A_860)
      | ~ r1_tarski(A_859,u1_struct_0(B_861)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3108])).

tff(c_3147,plain,(
    ! [A_859] :
      ( m1_subset_1(A_859,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_859,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_3141])).

tff(c_3156,plain,(
    ! [A_859] :
      ( m1_subset_1(A_859,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_859,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_3147])).

tff(c_3085,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_3076])).

tff(c_3094,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3085])).

tff(c_3305,plain,(
    ! [A_859] :
      ( k1_tops_1('#skF_4',A_859) = A_859
      | ~ v3_pre_topc(A_859,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_859,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3156,c_3296])).

tff(c_3345,plain,(
    ! [A_881] :
      ( k1_tops_1('#skF_4',A_881) = A_881
      | ~ v3_pre_topc(A_881,'#skF_4')
      | ~ r1_tarski(A_881,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_3305])).

tff(c_3363,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_3345])).

tff(c_3364,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3363])).

tff(c_3169,plain,(
    ! [A_864] :
      ( m1_subset_1(A_864,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_864,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_3147])).

tff(c_3195,plain,(
    ! [A_868] :
      ( r1_tarski(A_868,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_868,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3169,c_2])).

tff(c_3206,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_3195])).

tff(c_3470,plain,(
    ! [B_888,A_889] :
      ( k1_tops_1(B_888,A_889) = A_889
      | ~ v3_pre_topc(A_889,B_888)
      | ~ l1_pre_topc(B_888)
      | ~ r1_tarski(A_889,u1_struct_0(B_888)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3296])).

tff(c_3491,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_3470])).

tff(c_3508,plain,
    ( k1_tops_1('#skF_3','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_3491])).

tff(c_3509,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3508])).

tff(c_3177,plain,(
    ! [D_865,C_866,A_867] :
      ( v3_pre_topc(D_865,C_866)
      | ~ m1_subset_1(D_865,k1_zfmisc_1(u1_struct_0(C_866)))
      | ~ v3_pre_topc(D_865,A_867)
      | ~ m1_pre_topc(C_866,A_867)
      | ~ m1_subset_1(D_865,k1_zfmisc_1(u1_struct_0(A_867)))
      | ~ l1_pre_topc(A_867) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4059,plain,(
    ! [A_954,C_955,A_956] :
      ( v3_pre_topc(A_954,C_955)
      | ~ v3_pre_topc(A_954,A_956)
      | ~ m1_pre_topc(C_955,A_956)
      | ~ m1_subset_1(A_954,k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ l1_pre_topc(A_956)
      | ~ r1_tarski(A_954,u1_struct_0(C_955)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3177])).

tff(c_4063,plain,(
    ! [A_954] :
      ( v3_pre_topc(A_954,'#skF_3')
      | ~ v3_pre_topc(A_954,'#skF_2')
      | ~ m1_subset_1(A_954,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_954,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_4059])).

tff(c_4078,plain,(
    ! [A_957] :
      ( v3_pre_topc(A_957,'#skF_3')
      | ~ v3_pre_topc(A_957,'#skF_2')
      | ~ m1_subset_1(A_957,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_957,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4063])).

tff(c_4107,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_4078])).

tff(c_4126,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_4107])).

tff(c_4128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3509,c_4126])).

tff(c_4129,plain,(
    k1_tops_1('#skF_3','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3508])).

tff(c_4445,plain,(
    ! [C_982,A_983,B_984] :
      ( m1_connsp_2(C_982,A_983,B_984)
      | ~ r2_hidden(B_984,k1_tops_1(A_983,C_982))
      | ~ m1_subset_1(C_982,k1_zfmisc_1(u1_struct_0(A_983)))
      | ~ m1_subset_1(B_984,u1_struct_0(A_983))
      | ~ l1_pre_topc(A_983)
      | ~ v2_pre_topc(A_983)
      | v2_struct_0(A_983) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4449,plain,(
    ! [B_984] :
      ( m1_connsp_2('#skF_6','#skF_3',B_984)
      | ~ r2_hidden(B_984,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_984,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4129,c_4445])).

tff(c_4457,plain,(
    ! [B_984] :
      ( m1_connsp_2('#skF_6','#skF_3',B_984)
      | ~ r2_hidden(B_984,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_984,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3088,c_107,c_4449])).

tff(c_4458,plain,(
    ! [B_984] :
      ( m1_connsp_2('#skF_6','#skF_3',B_984)
      | ~ r2_hidden(B_984,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_984,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4457])).

tff(c_4463,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4458])).

tff(c_4478,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_4463])).

tff(c_4494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4478])).

tff(c_4496,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4458])).

tff(c_4536,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_4496,c_10])).

tff(c_4884,plain,(
    ! [A_1028,C_1029,A_1030] :
      ( v3_pre_topc(A_1028,C_1029)
      | ~ v3_pre_topc(A_1028,A_1030)
      | ~ m1_pre_topc(C_1029,A_1030)
      | ~ m1_subset_1(A_1028,k1_zfmisc_1(u1_struct_0(A_1030)))
      | ~ l1_pre_topc(A_1030)
      | ~ r1_tarski(A_1028,u1_struct_0(C_1029)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3177])).

tff(c_4892,plain,(
    ! [A_1028] :
      ( v3_pre_topc(A_1028,'#skF_4')
      | ~ v3_pre_topc(A_1028,'#skF_2')
      | ~ m1_subset_1(A_1028,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_1028,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_4884])).

tff(c_5074,plain,(
    ! [A_1038] :
      ( v3_pre_topc(A_1038,'#skF_4')
      | ~ v3_pre_topc(A_1038,'#skF_2')
      | ~ m1_subset_1(A_1038,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_1038,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4892])).

tff(c_5078,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4536,c_5074])).

tff(c_5110,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_3206,c_34,c_5078])).

tff(c_5112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3364,c_5110])).

tff(c_5113,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3363])).

tff(c_5493,plain,(
    ! [C_1062,A_1063,B_1064] :
      ( m1_connsp_2(C_1062,A_1063,B_1064)
      | ~ r2_hidden(B_1064,k1_tops_1(A_1063,C_1062))
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(u1_struct_0(A_1063)))
      | ~ m1_subset_1(B_1064,u1_struct_0(A_1063))
      | ~ l1_pre_topc(A_1063)
      | ~ v2_pre_topc(A_1063)
      | v2_struct_0(A_1063) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5495,plain,(
    ! [B_1064] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1064)
      | ~ r2_hidden(B_1064,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1064,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_5493])).

tff(c_5499,plain,(
    ! [B_1064] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1064)
      | ~ r2_hidden(B_1064,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1064,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_111,c_5495])).

tff(c_5500,plain,(
    ! [B_1064] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1064)
      | ~ r2_hidden(B_1064,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1064,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5499])).

tff(c_5541,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_5500])).

tff(c_5553,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3156,c_5541])).

tff(c_5572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5553])).

tff(c_5574,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_5500])).

tff(c_5596,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_4',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_5574,c_10])).

tff(c_5967,plain,(
    ! [A_1123,C_1124,A_1125] :
      ( v3_pre_topc(A_1123,C_1124)
      | ~ v3_pre_topc(A_1123,A_1125)
      | ~ m1_pre_topc(C_1124,A_1125)
      | ~ m1_subset_1(A_1123,k1_zfmisc_1(u1_struct_0(A_1125)))
      | ~ l1_pre_topc(A_1125)
      | ~ r1_tarski(A_1123,u1_struct_0(C_1124)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3177])).

tff(c_5971,plain,(
    ! [A_1123] :
      ( v3_pre_topc(A_1123,'#skF_3')
      | ~ v3_pre_topc(A_1123,'#skF_2')
      | ~ m1_subset_1(A_1123,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_1123,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_5967])).

tff(c_5986,plain,(
    ! [A_1126] :
      ( v3_pre_topc(A_1126,'#skF_3')
      | ~ v3_pre_topc(A_1126,'#skF_2')
      | ~ m1_subset_1(A_1126,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_1126,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5971])).

tff(c_5990,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_5596,c_5986])).

tff(c_6022,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_30,c_34,c_5990])).

tff(c_6024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5252,c_6022])).

tff(c_6025,plain,(
    k1_tops_1('#skF_3','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5251])).

tff(c_6307,plain,(
    ! [C_1147,A_1148,B_1149] :
      ( m1_connsp_2(C_1147,A_1148,B_1149)
      | ~ r2_hidden(B_1149,k1_tops_1(A_1148,C_1147))
      | ~ m1_subset_1(C_1147,k1_zfmisc_1(u1_struct_0(A_1148)))
      | ~ m1_subset_1(B_1149,u1_struct_0(A_1148))
      | ~ l1_pre_topc(A_1148)
      | ~ v2_pre_topc(A_1148)
      | v2_struct_0(A_1148) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6309,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_3',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6025,c_6307])).

tff(c_6315,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_3',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3088,c_107,c_6309])).

tff(c_6316,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_3',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6315])).

tff(c_6325,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6316])).

tff(c_6340,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_6325])).

tff(c_6356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6340])).

tff(c_6358,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6316])).

tff(c_6380,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_6358,c_10])).

tff(c_6311,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5113,c_6307])).

tff(c_6318,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_111,c_6311])).

tff(c_6319,plain,(
    ! [B_1149] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1149)
      | ~ r2_hidden(B_1149,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1149,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6318])).

tff(c_6543,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6319])).

tff(c_6546,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6380,c_6543])).

tff(c_6568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_42,c_6546])).

tff(c_6570,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6319])).

tff(c_6623,plain,(
    ! [B_1160] :
      ( m1_connsp_2('#skF_6','#skF_4',B_1160)
      | ~ r2_hidden(B_1160,'#skF_6')
      | ~ m1_subset_1(B_1160,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_6319])).

tff(c_6626,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_79,c_6623])).

tff(c_6629,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6626])).

tff(c_6732,plain,(
    ! [C_1178,A_1180,D_1183,F_1177,B_1179,H_1181,E_1182] :
      ( r1_tmap_1(C_1178,B_1179,k3_tmap_1(A_1180,B_1179,D_1183,C_1178,E_1182),H_1181)
      | ~ r1_tmap_1(D_1183,B_1179,E_1182,H_1181)
      | ~ m1_connsp_2(F_1177,D_1183,H_1181)
      | ~ r1_tarski(F_1177,u1_struct_0(C_1178))
      | ~ m1_subset_1(H_1181,u1_struct_0(C_1178))
      | ~ m1_subset_1(H_1181,u1_struct_0(D_1183))
      | ~ m1_subset_1(F_1177,k1_zfmisc_1(u1_struct_0(D_1183)))
      | ~ m1_pre_topc(C_1178,D_1183)
      | ~ m1_subset_1(E_1182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1183),u1_struct_0(B_1179))))
      | ~ v1_funct_2(E_1182,u1_struct_0(D_1183),u1_struct_0(B_1179))
      | ~ v1_funct_1(E_1182)
      | ~ m1_pre_topc(D_1183,A_1180)
      | v2_struct_0(D_1183)
      | ~ m1_pre_topc(C_1178,A_1180)
      | v2_struct_0(C_1178)
      | ~ l1_pre_topc(B_1179)
      | ~ v2_pre_topc(B_1179)
      | v2_struct_0(B_1179)
      | ~ l1_pre_topc(A_1180)
      | ~ v2_pre_topc(A_1180)
      | v2_struct_0(A_1180) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6734,plain,(
    ! [C_1178,B_1179,A_1180,E_1182] :
      ( r1_tmap_1(C_1178,B_1179,k3_tmap_1(A_1180,B_1179,'#skF_4',C_1178,E_1182),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_1179,E_1182,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1178))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1178))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_1178,'#skF_4')
      | ~ m1_subset_1(E_1182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1179))))
      | ~ v1_funct_2(E_1182,u1_struct_0('#skF_4'),u1_struct_0(B_1179))
      | ~ v1_funct_1(E_1182)
      | ~ m1_pre_topc('#skF_4',A_1180)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_1178,A_1180)
      | v2_struct_0(C_1178)
      | ~ l1_pre_topc(B_1179)
      | ~ v2_pre_topc(B_1179)
      | v2_struct_0(B_1179)
      | ~ l1_pre_topc(A_1180)
      | ~ v2_pre_topc(A_1180)
      | v2_struct_0(A_1180) ) ),
    inference(resolution,[status(thm)],[c_6629,c_6732])).

tff(c_6739,plain,(
    ! [C_1178,B_1179,A_1180,E_1182] :
      ( r1_tmap_1(C_1178,B_1179,k3_tmap_1(A_1180,B_1179,'#skF_4',C_1178,E_1182),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_1179,E_1182,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1178))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1178))
      | ~ m1_pre_topc(C_1178,'#skF_4')
      | ~ m1_subset_1(E_1182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1179))))
      | ~ v1_funct_2(E_1182,u1_struct_0('#skF_4'),u1_struct_0(B_1179))
      | ~ v1_funct_1(E_1182)
      | ~ m1_pre_topc('#skF_4',A_1180)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_1178,A_1180)
      | v2_struct_0(C_1178)
      | ~ l1_pre_topc(B_1179)
      | ~ v2_pre_topc(B_1179)
      | v2_struct_0(B_1179)
      | ~ l1_pre_topc(A_1180)
      | ~ v2_pre_topc(A_1180)
      | v2_struct_0(A_1180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6570,c_79,c_6734])).

tff(c_7153,plain,(
    ! [C_1214,B_1215,A_1216,E_1217] :
      ( r1_tmap_1(C_1214,B_1215,k3_tmap_1(A_1216,B_1215,'#skF_4',C_1214,E_1217),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_1215,E_1217,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1214))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1214))
      | ~ m1_pre_topc(C_1214,'#skF_4')
      | ~ m1_subset_1(E_1217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1215))))
      | ~ v1_funct_2(E_1217,u1_struct_0('#skF_4'),u1_struct_0(B_1215))
      | ~ v1_funct_1(E_1217)
      | ~ m1_pre_topc('#skF_4',A_1216)
      | ~ m1_pre_topc(C_1214,A_1216)
      | v2_struct_0(C_1214)
      | ~ l1_pre_topc(B_1215)
      | ~ v2_pre_topc(B_1215)
      | v2_struct_0(B_1215)
      | ~ l1_pre_topc(A_1216)
      | ~ v2_pre_topc(A_1216)
      | v2_struct_0(A_1216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6739])).

tff(c_7155,plain,(
    ! [C_1214,A_1216] :
      ( r1_tmap_1(C_1214,'#skF_1',k3_tmap_1(A_1216,'#skF_1','#skF_4',C_1214,'#skF_5'),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1214))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1214))
      | ~ m1_pre_topc(C_1214,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_1216)
      | ~ m1_pre_topc(C_1214,A_1216)
      | v2_struct_0(C_1214)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_1216)
      | ~ v2_pre_topc(A_1216)
      | v2_struct_0(A_1216) ) ),
    inference(resolution,[status(thm)],[c_44,c_7153])).

tff(c_7161,plain,(
    ! [C_1214,A_1216] :
      ( r1_tmap_1(C_1214,'#skF_1',k3_tmap_1(A_1216,'#skF_1','#skF_4',C_1214,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1214))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1214))
      | ~ m1_pre_topc(C_1214,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_1216)
      | ~ m1_pre_topc(C_1214,A_1216)
      | v2_struct_0(C_1214)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_1216)
      | ~ v2_pre_topc(A_1216)
      | v2_struct_0(A_1216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_3075,c_7155])).

tff(c_7271,plain,(
    ! [C_1222,A_1223] :
      ( r1_tmap_1(C_1222,'#skF_1',k3_tmap_1(A_1223,'#skF_1','#skF_4',C_1222,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_1222))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_1222))
      | ~ m1_pre_topc(C_1222,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_1223)
      | ~ m1_pre_topc(C_1222,A_1223)
      | v2_struct_0(C_1222)
      | ~ l1_pre_topc(A_1223)
      | ~ v2_pre_topc(A_1223)
      | v2_struct_0(A_1223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7161])).

tff(c_3074,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_7276,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7271,c_3074])).

tff(c_7283,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_42,c_36,c_30,c_7276])).

tff(c_7285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_7283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.89/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.89/2.37  
% 6.89/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.89/2.37  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 6.89/2.37  
% 6.89/2.37  %Foreground sorts:
% 6.89/2.37  
% 6.89/2.37  
% 6.89/2.37  %Background operators:
% 6.89/2.37  
% 6.89/2.37  
% 6.89/2.37  %Foreground operators:
% 6.89/2.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.89/2.37  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.89/2.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.89/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.89/2.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.89/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.89/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.89/2.37  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.89/2.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.89/2.37  tff('#skF_7', type, '#skF_7': $i).
% 6.89/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.89/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.89/2.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.89/2.37  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.89/2.37  tff('#skF_6', type, '#skF_6': $i).
% 6.89/2.37  tff('#skF_2', type, '#skF_2': $i).
% 6.89/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.89/2.37  tff('#skF_1', type, '#skF_1': $i).
% 6.89/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.89/2.37  tff('#skF_8', type, '#skF_8': $i).
% 6.89/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.89/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.89/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.89/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.89/2.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.89/2.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.89/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.89/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.89/2.37  
% 7.35/2.41  tff(f_235, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 7.35/2.41  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.35/2.41  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.35/2.41  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.35/2.41  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.35/2.41  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 7.35/2.41  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 7.35/2.41  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.35/2.41  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 7.35/2.41  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 7.35/2.41  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 7.35/2.41  tff(c_95, plain, (![B_566, A_567]: (l1_pre_topc(B_566) | ~m1_pre_topc(B_566, A_567) | ~l1_pre_topc(A_567))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.35/2.41  tff(c_104, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_95])).
% 7.35/2.41  tff(c_111, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_104])).
% 7.35/2.41  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.35/2.41  tff(c_167, plain, (![C_576, A_577, B_578]: (m1_subset_1(C_576, k1_zfmisc_1(u1_struct_0(A_577))) | ~m1_subset_1(C_576, k1_zfmisc_1(u1_struct_0(B_578))) | ~m1_pre_topc(B_578, A_577) | ~l1_pre_topc(A_577))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.35/2.41  tff(c_184, plain, (![A_581, A_582, B_583]: (m1_subset_1(A_581, k1_zfmisc_1(u1_struct_0(A_582))) | ~m1_pre_topc(B_583, A_582) | ~l1_pre_topc(A_582) | ~r1_tarski(A_581, u1_struct_0(B_583)))), inference(resolution, [status(thm)], [c_4, c_167])).
% 7.35/2.41  tff(c_190, plain, (![A_581]: (m1_subset_1(A_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_581, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_184])).
% 7.35/2.41  tff(c_199, plain, (![A_581]: (m1_subset_1(A_581, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_581, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_190])).
% 7.35/2.41  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_119, plain, (![B_568, A_569]: (v2_pre_topc(B_568) | ~m1_pre_topc(B_568, A_569) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.35/2.41  tff(c_128, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_119])).
% 7.35/2.41  tff(c_137, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_128])).
% 7.35/2.41  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_14, plain, (![B_24, D_30, C_28, A_16]: (k1_tops_1(B_24, D_30)=D_30 | ~v3_pre_topc(D_30, B_24) | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0(B_24))) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(B_24) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.35/2.41  tff(c_285, plain, (![C_597, A_598]: (~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0(A_598))) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598))), inference(splitLeft, [status(thm)], [c_14])).
% 7.35/2.41  tff(c_307, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_285])).
% 7.35/2.41  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_307])).
% 7.35/2.41  tff(c_325, plain, (![B_599, D_600]: (k1_tops_1(B_599, D_600)=D_600 | ~v3_pre_topc(D_600, B_599) | ~m1_subset_1(D_600, k1_zfmisc_1(u1_struct_0(B_599))) | ~l1_pre_topc(B_599))), inference(splitRight, [status(thm)], [c_14])).
% 7.35/2.41  tff(c_334, plain, (![A_581]: (k1_tops_1('#skF_4', A_581)=A_581 | ~v3_pre_topc(A_581, '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_581, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_199, c_325])).
% 7.35/2.41  tff(c_374, plain, (![A_602]: (k1_tops_1('#skF_4', A_602)=A_602 | ~v3_pre_topc(A_602, '#skF_4') | ~r1_tarski(A_602, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_334])).
% 7.35/2.41  tff(c_385, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_374])).
% 7.35/2.41  tff(c_386, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_385])).
% 7.35/2.41  tff(c_227, plain, (![A_589]: (m1_subset_1(A_589, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_589, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_190])).
% 7.35/2.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.35/2.41  tff(c_238, plain, (![A_590]: (r1_tarski(A_590, u1_struct_0('#skF_4')) | ~r1_tarski(A_590, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_227, c_2])).
% 7.35/2.41  tff(c_249, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_238])).
% 7.35/2.41  tff(c_34, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_122, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_119])).
% 7.35/2.41  tff(c_131, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_122])).
% 7.35/2.41  tff(c_98, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_95])).
% 7.35/2.41  tff(c_107, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_98])).
% 7.35/2.41  tff(c_456, plain, (![B_607, A_608]: (k1_tops_1(B_607, A_608)=A_608 | ~v3_pre_topc(A_608, B_607) | ~l1_pre_topc(B_607) | ~r1_tarski(A_608, u1_struct_0(B_607)))), inference(resolution, [status(thm)], [c_4, c_325])).
% 7.35/2.41  tff(c_474, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_456])).
% 7.35/2.41  tff(c_490, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_474])).
% 7.35/2.41  tff(c_491, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_490])).
% 7.35/2.41  tff(c_211, plain, (![D_585, C_586, A_587]: (v3_pre_topc(D_585, C_586) | ~m1_subset_1(D_585, k1_zfmisc_1(u1_struct_0(C_586))) | ~v3_pre_topc(D_585, A_587) | ~m1_pre_topc(C_586, A_587) | ~m1_subset_1(D_585, k1_zfmisc_1(u1_struct_0(A_587))) | ~l1_pre_topc(A_587))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.35/2.41  tff(c_1167, plain, (![A_685, C_686, A_687]: (v3_pre_topc(A_685, C_686) | ~v3_pre_topc(A_685, A_687) | ~m1_pre_topc(C_686, A_687) | ~m1_subset_1(A_685, k1_zfmisc_1(u1_struct_0(A_687))) | ~l1_pre_topc(A_687) | ~r1_tarski(A_685, u1_struct_0(C_686)))), inference(resolution, [status(thm)], [c_4, c_211])).
% 7.35/2.41  tff(c_1171, plain, (![A_685]: (v3_pre_topc(A_685, '#skF_3') | ~v3_pre_topc(A_685, '#skF_2') | ~m1_subset_1(A_685, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_685, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_1167])).
% 7.35/2.41  tff(c_1186, plain, (![A_688]: (v3_pre_topc(A_688, '#skF_3') | ~v3_pre_topc(A_688, '#skF_2') | ~m1_subset_1(A_688, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_688, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1171])).
% 7.35/2.41  tff(c_1215, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_1186])).
% 7.35/2.41  tff(c_1234, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_1215])).
% 7.35/2.41  tff(c_1236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_1234])).
% 7.35/2.41  tff(c_1237, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_490])).
% 7.35/2.41  tff(c_1523, plain, (![C_710, A_711, B_712]: (m1_connsp_2(C_710, A_711, B_712) | ~r2_hidden(B_712, k1_tops_1(A_711, C_710)) | ~m1_subset_1(C_710, k1_zfmisc_1(u1_struct_0(A_711))) | ~m1_subset_1(B_712, u1_struct_0(A_711)) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.35/2.41  tff(c_1527, plain, (![B_712]: (m1_connsp_2('#skF_6', '#skF_3', B_712) | ~r2_hidden(B_712, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_712, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1237, c_1523])).
% 7.35/2.41  tff(c_1535, plain, (![B_712]: (m1_connsp_2('#skF_6', '#skF_3', B_712) | ~r2_hidden(B_712, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_712, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_107, c_1527])).
% 7.35/2.41  tff(c_1536, plain, (![B_712]: (m1_connsp_2('#skF_6', '#skF_3', B_712) | ~r2_hidden(B_712, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_712, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1535])).
% 7.35/2.41  tff(c_1558, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1536])).
% 7.35/2.41  tff(c_1573, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1558])).
% 7.35/2.41  tff(c_1589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1573])).
% 7.35/2.41  tff(c_1591, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1536])).
% 7.35/2.41  tff(c_10, plain, (![C_15, A_9, B_13]: (m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_13))) | ~m1_pre_topc(B_13, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.35/2.41  tff(c_1619, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_1591, c_10])).
% 7.35/2.41  tff(c_1957, plain, (![A_746, C_747, A_748]: (v3_pre_topc(A_746, C_747) | ~v3_pre_topc(A_746, A_748) | ~m1_pre_topc(C_747, A_748) | ~m1_subset_1(A_746, k1_zfmisc_1(u1_struct_0(A_748))) | ~l1_pre_topc(A_748) | ~r1_tarski(A_746, u1_struct_0(C_747)))), inference(resolution, [status(thm)], [c_4, c_211])).
% 7.35/2.41  tff(c_1965, plain, (![A_746]: (v3_pre_topc(A_746, '#skF_4') | ~v3_pre_topc(A_746, '#skF_2') | ~m1_subset_1(A_746, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_746, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_1957])).
% 7.35/2.41  tff(c_2152, plain, (![A_760]: (v3_pre_topc(A_760, '#skF_4') | ~v3_pre_topc(A_760, '#skF_2') | ~m1_subset_1(A_760, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_760, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1965])).
% 7.35/2.41  tff(c_2156, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1619, c_2152])).
% 7.35/2.41  tff(c_2188, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_249, c_34, c_2156])).
% 7.35/2.41  tff(c_2190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_2188])).
% 7.35/2.41  tff(c_2191, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_385])).
% 7.35/2.41  tff(c_2737, plain, (![C_800, A_801, B_802]: (m1_connsp_2(C_800, A_801, B_802) | ~r2_hidden(B_802, k1_tops_1(A_801, C_800)) | ~m1_subset_1(C_800, k1_zfmisc_1(u1_struct_0(A_801))) | ~m1_subset_1(B_802, u1_struct_0(A_801)) | ~l1_pre_topc(A_801) | ~v2_pre_topc(A_801) | v2_struct_0(A_801))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.35/2.41  tff(c_2741, plain, (![B_802]: (m1_connsp_2('#skF_6', '#skF_4', B_802) | ~r2_hidden(B_802, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_802, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2191, c_2737])).
% 7.35/2.41  tff(c_2749, plain, (![B_802]: (m1_connsp_2('#skF_6', '#skF_4', B_802) | ~r2_hidden(B_802, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_802, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_111, c_2741])).
% 7.35/2.41  tff(c_2750, plain, (![B_802]: (m1_connsp_2('#skF_6', '#skF_4', B_802) | ~r2_hidden(B_802, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_802, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_2749])).
% 7.35/2.41  tff(c_2755, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2750])).
% 7.35/2.41  tff(c_2767, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_199, c_2755])).
% 7.35/2.41  tff(c_2786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2767])).
% 7.35/2.41  tff(c_2853, plain, (![B_807]: (m1_connsp_2('#skF_6', '#skF_4', B_807) | ~r2_hidden(B_807, '#skF_6') | ~m1_subset_1(B_807, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2750])).
% 7.35/2.41  tff(c_2856, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_79, c_2853])).
% 7.35/2.41  tff(c_2859, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2856])).
% 7.35/2.41  tff(c_2788, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2750])).
% 7.35/2.41  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 7.35/2.41  tff(c_118, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_78])).
% 7.35/2.41  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.35/2.41  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 7.35/2.41  tff(c_166, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_118, c_77])).
% 7.35/2.41  tff(c_3029, plain, (![F_838, B_840, C_839, E_843, A_841, D_844, H_842]: (r1_tmap_1(D_844, B_840, E_843, H_842) | ~r1_tmap_1(C_839, B_840, k3_tmap_1(A_841, B_840, D_844, C_839, E_843), H_842) | ~m1_connsp_2(F_838, D_844, H_842) | ~r1_tarski(F_838, u1_struct_0(C_839)) | ~m1_subset_1(H_842, u1_struct_0(C_839)) | ~m1_subset_1(H_842, u1_struct_0(D_844)) | ~m1_subset_1(F_838, k1_zfmisc_1(u1_struct_0(D_844))) | ~m1_pre_topc(C_839, D_844) | ~m1_subset_1(E_843, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_844), u1_struct_0(B_840)))) | ~v1_funct_2(E_843, u1_struct_0(D_844), u1_struct_0(B_840)) | ~v1_funct_1(E_843) | ~m1_pre_topc(D_844, A_841) | v2_struct_0(D_844) | ~m1_pre_topc(C_839, A_841) | v2_struct_0(C_839) | ~l1_pre_topc(B_840) | ~v2_pre_topc(B_840) | v2_struct_0(B_840) | ~l1_pre_topc(A_841) | ~v2_pre_topc(A_841) | v2_struct_0(A_841))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.35/2.42  tff(c_3031, plain, (![F_838]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_connsp_2(F_838, '#skF_4', '#skF_8') | ~r1_tarski(F_838, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_838, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_166, c_3029])).
% 7.35/2.42  tff(c_3034, plain, (![F_838]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_connsp_2(F_838, '#skF_4', '#skF_8') | ~r1_tarski(F_838, u1_struct_0('#skF_3')) | ~m1_subset_1(F_838, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_66, c_64, c_54, c_50, c_48, c_46, c_44, c_42, c_79, c_36, c_3031])).
% 7.35/2.42  tff(c_3036, plain, (![F_845]: (~m1_connsp_2(F_845, '#skF_4', '#skF_8') | ~r1_tarski(F_845, u1_struct_0('#skF_3')) | ~m1_subset_1(F_845, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_56, c_52, c_118, c_3034])).
% 7.35/2.42  tff(c_3043, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2788, c_3036])).
% 7.35/2.42  tff(c_3073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2859, c_3043])).
% 7.35/2.42  tff(c_3075, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 7.35/2.42  tff(c_3076, plain, (![B_846, A_847]: (v2_pre_topc(B_846) | ~m1_pre_topc(B_846, A_847) | ~l1_pre_topc(A_847) | ~v2_pre_topc(A_847))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.35/2.42  tff(c_3079, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3076])).
% 7.35/2.42  tff(c_3088, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3079])).
% 7.35/2.42  tff(c_3256, plain, (![C_876, A_877]: (~m1_subset_1(C_876, k1_zfmisc_1(u1_struct_0(A_877))) | ~l1_pre_topc(A_877) | ~v2_pre_topc(A_877))), inference(splitLeft, [status(thm)], [c_14])).
% 7.35/2.42  tff(c_3278, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_3256])).
% 7.35/2.42  tff(c_3294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3278])).
% 7.35/2.42  tff(c_3296, plain, (![B_878, D_879]: (k1_tops_1(B_878, D_879)=D_879 | ~v3_pre_topc(D_879, B_878) | ~m1_subset_1(D_879, k1_zfmisc_1(u1_struct_0(B_878))) | ~l1_pre_topc(B_878))), inference(splitRight, [status(thm)], [c_14])).
% 7.35/2.42  tff(c_5213, plain, (![B_1043, A_1044]: (k1_tops_1(B_1043, A_1044)=A_1044 | ~v3_pre_topc(A_1044, B_1043) | ~l1_pre_topc(B_1043) | ~r1_tarski(A_1044, u1_struct_0(B_1043)))), inference(resolution, [status(thm)], [c_4, c_3296])).
% 7.35/2.42  tff(c_5234, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_5213])).
% 7.35/2.42  tff(c_5251, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_5234])).
% 7.35/2.42  tff(c_5252, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_5251])).
% 7.35/2.42  tff(c_3108, plain, (![C_851, A_852, B_853]: (m1_subset_1(C_851, k1_zfmisc_1(u1_struct_0(A_852))) | ~m1_subset_1(C_851, k1_zfmisc_1(u1_struct_0(B_853))) | ~m1_pre_topc(B_853, A_852) | ~l1_pre_topc(A_852))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.35/2.42  tff(c_3141, plain, (![A_859, A_860, B_861]: (m1_subset_1(A_859, k1_zfmisc_1(u1_struct_0(A_860))) | ~m1_pre_topc(B_861, A_860) | ~l1_pre_topc(A_860) | ~r1_tarski(A_859, u1_struct_0(B_861)))), inference(resolution, [status(thm)], [c_4, c_3108])).
% 7.35/2.42  tff(c_3147, plain, (![A_859]: (m1_subset_1(A_859, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_859, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_3141])).
% 7.35/2.42  tff(c_3156, plain, (![A_859]: (m1_subset_1(A_859, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_859, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_3147])).
% 7.35/2.42  tff(c_3085, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_3076])).
% 7.35/2.42  tff(c_3094, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3085])).
% 7.35/2.42  tff(c_3305, plain, (![A_859]: (k1_tops_1('#skF_4', A_859)=A_859 | ~v3_pre_topc(A_859, '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_859, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3156, c_3296])).
% 7.35/2.42  tff(c_3345, plain, (![A_881]: (k1_tops_1('#skF_4', A_881)=A_881 | ~v3_pre_topc(A_881, '#skF_4') | ~r1_tarski(A_881, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_3305])).
% 7.35/2.42  tff(c_3363, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_3345])).
% 7.35/2.42  tff(c_3364, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_3363])).
% 7.35/2.42  tff(c_3169, plain, (![A_864]: (m1_subset_1(A_864, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_864, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_3147])).
% 7.35/2.42  tff(c_3195, plain, (![A_868]: (r1_tarski(A_868, u1_struct_0('#skF_4')) | ~r1_tarski(A_868, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3169, c_2])).
% 7.35/2.42  tff(c_3206, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_3195])).
% 7.35/2.42  tff(c_3470, plain, (![B_888, A_889]: (k1_tops_1(B_888, A_889)=A_889 | ~v3_pre_topc(A_889, B_888) | ~l1_pre_topc(B_888) | ~r1_tarski(A_889, u1_struct_0(B_888)))), inference(resolution, [status(thm)], [c_4, c_3296])).
% 7.35/2.42  tff(c_3491, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_3470])).
% 7.35/2.42  tff(c_3508, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_3491])).
% 7.35/2.42  tff(c_3509, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_3508])).
% 7.35/2.42  tff(c_3177, plain, (![D_865, C_866, A_867]: (v3_pre_topc(D_865, C_866) | ~m1_subset_1(D_865, k1_zfmisc_1(u1_struct_0(C_866))) | ~v3_pre_topc(D_865, A_867) | ~m1_pre_topc(C_866, A_867) | ~m1_subset_1(D_865, k1_zfmisc_1(u1_struct_0(A_867))) | ~l1_pre_topc(A_867))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.35/2.42  tff(c_4059, plain, (![A_954, C_955, A_956]: (v3_pre_topc(A_954, C_955) | ~v3_pre_topc(A_954, A_956) | ~m1_pre_topc(C_955, A_956) | ~m1_subset_1(A_954, k1_zfmisc_1(u1_struct_0(A_956))) | ~l1_pre_topc(A_956) | ~r1_tarski(A_954, u1_struct_0(C_955)))), inference(resolution, [status(thm)], [c_4, c_3177])).
% 7.35/2.42  tff(c_4063, plain, (![A_954]: (v3_pre_topc(A_954, '#skF_3') | ~v3_pre_topc(A_954, '#skF_2') | ~m1_subset_1(A_954, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_954, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_4059])).
% 7.35/2.42  tff(c_4078, plain, (![A_957]: (v3_pre_topc(A_957, '#skF_3') | ~v3_pre_topc(A_957, '#skF_2') | ~m1_subset_1(A_957, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_957, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4063])).
% 7.35/2.42  tff(c_4107, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_4078])).
% 7.35/2.42  tff(c_4126, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_4107])).
% 7.35/2.42  tff(c_4128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3509, c_4126])).
% 7.35/2.42  tff(c_4129, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_3508])).
% 7.35/2.42  tff(c_4445, plain, (![C_982, A_983, B_984]: (m1_connsp_2(C_982, A_983, B_984) | ~r2_hidden(B_984, k1_tops_1(A_983, C_982)) | ~m1_subset_1(C_982, k1_zfmisc_1(u1_struct_0(A_983))) | ~m1_subset_1(B_984, u1_struct_0(A_983)) | ~l1_pre_topc(A_983) | ~v2_pre_topc(A_983) | v2_struct_0(A_983))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.35/2.42  tff(c_4449, plain, (![B_984]: (m1_connsp_2('#skF_6', '#skF_3', B_984) | ~r2_hidden(B_984, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_984, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4129, c_4445])).
% 7.35/2.42  tff(c_4457, plain, (![B_984]: (m1_connsp_2('#skF_6', '#skF_3', B_984) | ~r2_hidden(B_984, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_984, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3088, c_107, c_4449])).
% 7.35/2.42  tff(c_4458, plain, (![B_984]: (m1_connsp_2('#skF_6', '#skF_3', B_984) | ~r2_hidden(B_984, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_984, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_4457])).
% 7.35/2.42  tff(c_4463, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_4458])).
% 7.35/2.42  tff(c_4478, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_4463])).
% 7.35/2.42  tff(c_4494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4478])).
% 7.35/2.42  tff(c_4496, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_4458])).
% 7.35/2.42  tff(c_4536, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_4496, c_10])).
% 7.35/2.42  tff(c_4884, plain, (![A_1028, C_1029, A_1030]: (v3_pre_topc(A_1028, C_1029) | ~v3_pre_topc(A_1028, A_1030) | ~m1_pre_topc(C_1029, A_1030) | ~m1_subset_1(A_1028, k1_zfmisc_1(u1_struct_0(A_1030))) | ~l1_pre_topc(A_1030) | ~r1_tarski(A_1028, u1_struct_0(C_1029)))), inference(resolution, [status(thm)], [c_4, c_3177])).
% 7.35/2.42  tff(c_4892, plain, (![A_1028]: (v3_pre_topc(A_1028, '#skF_4') | ~v3_pre_topc(A_1028, '#skF_2') | ~m1_subset_1(A_1028, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_1028, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_4884])).
% 7.35/2.42  tff(c_5074, plain, (![A_1038]: (v3_pre_topc(A_1038, '#skF_4') | ~v3_pre_topc(A_1038, '#skF_2') | ~m1_subset_1(A_1038, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_1038, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4892])).
% 7.35/2.42  tff(c_5078, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4536, c_5074])).
% 7.35/2.42  tff(c_5110, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_3206, c_34, c_5078])).
% 7.35/2.42  tff(c_5112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3364, c_5110])).
% 7.35/2.42  tff(c_5113, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_3363])).
% 7.35/2.42  tff(c_5493, plain, (![C_1062, A_1063, B_1064]: (m1_connsp_2(C_1062, A_1063, B_1064) | ~r2_hidden(B_1064, k1_tops_1(A_1063, C_1062)) | ~m1_subset_1(C_1062, k1_zfmisc_1(u1_struct_0(A_1063))) | ~m1_subset_1(B_1064, u1_struct_0(A_1063)) | ~l1_pre_topc(A_1063) | ~v2_pre_topc(A_1063) | v2_struct_0(A_1063))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.35/2.42  tff(c_5495, plain, (![B_1064]: (m1_connsp_2('#skF_6', '#skF_4', B_1064) | ~r2_hidden(B_1064, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1064, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5113, c_5493])).
% 7.35/2.42  tff(c_5499, plain, (![B_1064]: (m1_connsp_2('#skF_6', '#skF_4', B_1064) | ~r2_hidden(B_1064, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1064, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_111, c_5495])).
% 7.35/2.42  tff(c_5500, plain, (![B_1064]: (m1_connsp_2('#skF_6', '#skF_4', B_1064) | ~r2_hidden(B_1064, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1064, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_5499])).
% 7.35/2.42  tff(c_5541, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_5500])).
% 7.35/2.42  tff(c_5553, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3156, c_5541])).
% 7.35/2.42  tff(c_5572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_5553])).
% 7.35/2.42  tff(c_5574, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_5500])).
% 7.35/2.42  tff(c_5596, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_4', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_5574, c_10])).
% 7.35/2.42  tff(c_5967, plain, (![A_1123, C_1124, A_1125]: (v3_pre_topc(A_1123, C_1124) | ~v3_pre_topc(A_1123, A_1125) | ~m1_pre_topc(C_1124, A_1125) | ~m1_subset_1(A_1123, k1_zfmisc_1(u1_struct_0(A_1125))) | ~l1_pre_topc(A_1125) | ~r1_tarski(A_1123, u1_struct_0(C_1124)))), inference(resolution, [status(thm)], [c_4, c_3177])).
% 7.35/2.42  tff(c_5971, plain, (![A_1123]: (v3_pre_topc(A_1123, '#skF_3') | ~v3_pre_topc(A_1123, '#skF_2') | ~m1_subset_1(A_1123, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_1123, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_5967])).
% 7.35/2.42  tff(c_5986, plain, (![A_1126]: (v3_pre_topc(A_1126, '#skF_3') | ~v3_pre_topc(A_1126, '#skF_2') | ~m1_subset_1(A_1126, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_1126, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5971])).
% 7.35/2.42  tff(c_5990, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_5596, c_5986])).
% 7.35/2.42  tff(c_6022, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50, c_30, c_34, c_5990])).
% 7.35/2.42  tff(c_6024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5252, c_6022])).
% 7.35/2.42  tff(c_6025, plain, (k1_tops_1('#skF_3', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_5251])).
% 7.35/2.42  tff(c_6307, plain, (![C_1147, A_1148, B_1149]: (m1_connsp_2(C_1147, A_1148, B_1149) | ~r2_hidden(B_1149, k1_tops_1(A_1148, C_1147)) | ~m1_subset_1(C_1147, k1_zfmisc_1(u1_struct_0(A_1148))) | ~m1_subset_1(B_1149, u1_struct_0(A_1148)) | ~l1_pre_topc(A_1148) | ~v2_pre_topc(A_1148) | v2_struct_0(A_1148))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.35/2.42  tff(c_6309, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_3', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6025, c_6307])).
% 7.35/2.42  tff(c_6315, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_3', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3088, c_107, c_6309])).
% 7.35/2.42  tff(c_6316, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_3', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_6315])).
% 7.35/2.42  tff(c_6325, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_6316])).
% 7.35/2.42  tff(c_6340, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_6325])).
% 7.35/2.42  tff(c_6356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_6340])).
% 7.35/2.42  tff(c_6358, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_6316])).
% 7.35/2.42  tff(c_6380, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_6358, c_10])).
% 7.35/2.42  tff(c_6311, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_4', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5113, c_6307])).
% 7.35/2.42  tff(c_6318, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_4', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_111, c_6311])).
% 7.35/2.42  tff(c_6319, plain, (![B_1149]: (m1_connsp_2('#skF_6', '#skF_4', B_1149) | ~r2_hidden(B_1149, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_1149, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_6318])).
% 7.35/2.42  tff(c_6543, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_6319])).
% 7.35/2.42  tff(c_6546, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6380, c_6543])).
% 7.35/2.42  tff(c_6568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_42, c_6546])).
% 7.35/2.42  tff(c_6570, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_6319])).
% 7.35/2.42  tff(c_6623, plain, (![B_1160]: (m1_connsp_2('#skF_6', '#skF_4', B_1160) | ~r2_hidden(B_1160, '#skF_6') | ~m1_subset_1(B_1160, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_6319])).
% 7.35/2.42  tff(c_6626, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_79, c_6623])).
% 7.35/2.42  tff(c_6629, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6626])).
% 7.35/2.42  tff(c_6732, plain, (![C_1178, A_1180, D_1183, F_1177, B_1179, H_1181, E_1182]: (r1_tmap_1(C_1178, B_1179, k3_tmap_1(A_1180, B_1179, D_1183, C_1178, E_1182), H_1181) | ~r1_tmap_1(D_1183, B_1179, E_1182, H_1181) | ~m1_connsp_2(F_1177, D_1183, H_1181) | ~r1_tarski(F_1177, u1_struct_0(C_1178)) | ~m1_subset_1(H_1181, u1_struct_0(C_1178)) | ~m1_subset_1(H_1181, u1_struct_0(D_1183)) | ~m1_subset_1(F_1177, k1_zfmisc_1(u1_struct_0(D_1183))) | ~m1_pre_topc(C_1178, D_1183) | ~m1_subset_1(E_1182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1183), u1_struct_0(B_1179)))) | ~v1_funct_2(E_1182, u1_struct_0(D_1183), u1_struct_0(B_1179)) | ~v1_funct_1(E_1182) | ~m1_pre_topc(D_1183, A_1180) | v2_struct_0(D_1183) | ~m1_pre_topc(C_1178, A_1180) | v2_struct_0(C_1178) | ~l1_pre_topc(B_1179) | ~v2_pre_topc(B_1179) | v2_struct_0(B_1179) | ~l1_pre_topc(A_1180) | ~v2_pre_topc(A_1180) | v2_struct_0(A_1180))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.35/2.42  tff(c_6734, plain, (![C_1178, B_1179, A_1180, E_1182]: (r1_tmap_1(C_1178, B_1179, k3_tmap_1(A_1180, B_1179, '#skF_4', C_1178, E_1182), '#skF_8') | ~r1_tmap_1('#skF_4', B_1179, E_1182, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1178)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1178)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_1178, '#skF_4') | ~m1_subset_1(E_1182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1179)))) | ~v1_funct_2(E_1182, u1_struct_0('#skF_4'), u1_struct_0(B_1179)) | ~v1_funct_1(E_1182) | ~m1_pre_topc('#skF_4', A_1180) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_1178, A_1180) | v2_struct_0(C_1178) | ~l1_pre_topc(B_1179) | ~v2_pre_topc(B_1179) | v2_struct_0(B_1179) | ~l1_pre_topc(A_1180) | ~v2_pre_topc(A_1180) | v2_struct_0(A_1180))), inference(resolution, [status(thm)], [c_6629, c_6732])).
% 7.35/2.42  tff(c_6739, plain, (![C_1178, B_1179, A_1180, E_1182]: (r1_tmap_1(C_1178, B_1179, k3_tmap_1(A_1180, B_1179, '#skF_4', C_1178, E_1182), '#skF_8') | ~r1_tmap_1('#skF_4', B_1179, E_1182, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1178)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1178)) | ~m1_pre_topc(C_1178, '#skF_4') | ~m1_subset_1(E_1182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1179)))) | ~v1_funct_2(E_1182, u1_struct_0('#skF_4'), u1_struct_0(B_1179)) | ~v1_funct_1(E_1182) | ~m1_pre_topc('#skF_4', A_1180) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_1178, A_1180) | v2_struct_0(C_1178) | ~l1_pre_topc(B_1179) | ~v2_pre_topc(B_1179) | v2_struct_0(B_1179) | ~l1_pre_topc(A_1180) | ~v2_pre_topc(A_1180) | v2_struct_0(A_1180))), inference(demodulation, [status(thm), theory('equality')], [c_6570, c_79, c_6734])).
% 7.35/2.42  tff(c_7153, plain, (![C_1214, B_1215, A_1216, E_1217]: (r1_tmap_1(C_1214, B_1215, k3_tmap_1(A_1216, B_1215, '#skF_4', C_1214, E_1217), '#skF_8') | ~r1_tmap_1('#skF_4', B_1215, E_1217, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1214)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1214)) | ~m1_pre_topc(C_1214, '#skF_4') | ~m1_subset_1(E_1217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1215)))) | ~v1_funct_2(E_1217, u1_struct_0('#skF_4'), u1_struct_0(B_1215)) | ~v1_funct_1(E_1217) | ~m1_pre_topc('#skF_4', A_1216) | ~m1_pre_topc(C_1214, A_1216) | v2_struct_0(C_1214) | ~l1_pre_topc(B_1215) | ~v2_pre_topc(B_1215) | v2_struct_0(B_1215) | ~l1_pre_topc(A_1216) | ~v2_pre_topc(A_1216) | v2_struct_0(A_1216))), inference(negUnitSimplification, [status(thm)], [c_52, c_6739])).
% 7.35/2.42  tff(c_7155, plain, (![C_1214, A_1216]: (r1_tmap_1(C_1214, '#skF_1', k3_tmap_1(A_1216, '#skF_1', '#skF_4', C_1214, '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1214)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1214)) | ~m1_pre_topc(C_1214, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_1216) | ~m1_pre_topc(C_1214, A_1216) | v2_struct_0(C_1214) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_1216) | ~v2_pre_topc(A_1216) | v2_struct_0(A_1216))), inference(resolution, [status(thm)], [c_44, c_7153])).
% 7.35/2.42  tff(c_7161, plain, (![C_1214, A_1216]: (r1_tmap_1(C_1214, '#skF_1', k3_tmap_1(A_1216, '#skF_1', '#skF_4', C_1214, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1214)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1214)) | ~m1_pre_topc(C_1214, '#skF_4') | ~m1_pre_topc('#skF_4', A_1216) | ~m1_pre_topc(C_1214, A_1216) | v2_struct_0(C_1214) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_1216) | ~v2_pre_topc(A_1216) | v2_struct_0(A_1216))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_3075, c_7155])).
% 7.35/2.42  tff(c_7271, plain, (![C_1222, A_1223]: (r1_tmap_1(C_1222, '#skF_1', k3_tmap_1(A_1223, '#skF_1', '#skF_4', C_1222, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_1222)) | ~m1_subset_1('#skF_8', u1_struct_0(C_1222)) | ~m1_pre_topc(C_1222, '#skF_4') | ~m1_pre_topc('#skF_4', A_1223) | ~m1_pre_topc(C_1222, A_1223) | v2_struct_0(C_1222) | ~l1_pre_topc(A_1223) | ~v2_pre_topc(A_1223) | v2_struct_0(A_1223))), inference(negUnitSimplification, [status(thm)], [c_68, c_7161])).
% 7.35/2.42  tff(c_3074, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 7.35/2.42  tff(c_7276, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7271, c_3074])).
% 7.35/2.42  tff(c_7283, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_42, c_36, c_30, c_7276])).
% 7.35/2.42  tff(c_7285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_7283])).
% 7.35/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.35/2.42  
% 7.35/2.42  Inference rules
% 7.35/2.42  ----------------------
% 7.35/2.42  #Ref     : 0
% 7.35/2.42  #Sup     : 1318
% 7.35/2.42  #Fact    : 0
% 7.35/2.42  #Define  : 0
% 7.35/2.42  #Split   : 28
% 7.35/2.42  #Chain   : 0
% 7.35/2.42  #Close   : 0
% 7.35/2.42  
% 7.35/2.42  Ordering : KBO
% 7.35/2.42  
% 7.35/2.42  Simplification rules
% 7.35/2.42  ----------------------
% 7.35/2.42  #Subsume      : 401
% 7.35/2.42  #Demod        : 1875
% 7.35/2.42  #Tautology    : 421
% 7.35/2.42  #SimpNegUnit  : 132
% 7.35/2.42  #BackRed      : 0
% 7.35/2.42  
% 7.35/2.42  #Partial instantiations: 0
% 7.35/2.42  #Strategies tried      : 1
% 7.35/2.42  
% 7.35/2.42  Timing (in seconds)
% 7.35/2.42  ----------------------
% 7.35/2.42  Preprocessing        : 0.41
% 7.35/2.42  Parsing              : 0.20
% 7.35/2.42  CNF conversion       : 0.06
% 7.35/2.42  Main loop            : 1.19
% 7.35/2.42  Inferencing          : 0.41
% 7.35/2.42  Reduction            : 0.42
% 7.35/2.42  Demodulation         : 0.30
% 7.35/2.42  BG Simplification    : 0.04
% 7.35/2.42  Subsumption          : 0.23
% 7.35/2.42  Abstraction          : 0.05
% 7.35/2.42  MUC search           : 0.00
% 7.35/2.42  Cooper               : 0.00
% 7.35/2.42  Total                : 1.68
% 7.35/2.42  Index Insertion      : 0.00
% 7.35/2.42  Index Deletion       : 0.00
% 7.35/2.42  Index Matching       : 0.00
% 7.35/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
