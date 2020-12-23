%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 446 expanded)
%              Number of leaves         :   38 ( 188 expanded)
%              Depth                    :   18
%              Number of atoms          :  506 (3940 expanded)
%              Number of equality atoms :   33 ( 192 expanded)
%              Maximal formula depth    :   30 (   6 average)
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

tff(f_304,negated_conjecture,(
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

tff(f_29,axiom,(
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

tff(f_78,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_105,axiom,(
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

tff(f_246,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_28,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_79,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_95,plain,(
    ! [B_656,A_657] :
      ( l1_pre_topc(B_656)
      | ~ m1_pre_topc(B_656,A_657)
      | ~ l1_pre_topc(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

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

tff(c_194,plain,(
    ! [C_675,A_676,B_677] :
      ( m1_subset_1(C_675,k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ m1_subset_1(C_675,k1_zfmisc_1(u1_struct_0(B_677)))
      | ~ m1_pre_topc(B_677,A_676)
      | ~ l1_pre_topc(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_220,plain,(
    ! [A_683,A_684,B_685] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0(A_684)))
      | ~ m1_pre_topc(B_685,A_684)
      | ~ l1_pre_topc(A_684)
      | ~ r1_tarski(A_683,u1_struct_0(B_685)) ) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_226,plain,(
    ! [A_683] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_683,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_220])).

tff(c_258,plain,(
    ! [A_688] :
      ( m1_subset_1(A_688,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_688,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_226])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    ! [A_692] :
      ( r1_tarski(A_692,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_692,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_298,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_287])).

tff(c_34,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_269,plain,(
    ! [D_689,C_690,A_691] :
      ( v3_pre_topc(D_689,C_690)
      | ~ m1_subset_1(D_689,k1_zfmisc_1(u1_struct_0(C_690)))
      | ~ v3_pre_topc(D_689,A_691)
      | ~ m1_pre_topc(C_690,A_691)
      | ~ m1_subset_1(D_689,k1_zfmisc_1(u1_struct_0(A_691)))
      | ~ l1_pre_topc(A_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_615,plain,(
    ! [A_754,C_755,A_756] :
      ( v3_pre_topc(A_754,C_755)
      | ~ v3_pre_topc(A_754,A_756)
      | ~ m1_pre_topc(C_755,A_756)
      | ~ m1_subset_1(A_754,k1_zfmisc_1(u1_struct_0(A_756)))
      | ~ l1_pre_topc(A_756)
      | ~ r1_tarski(A_754,u1_struct_0(C_755)) ) ),
    inference(resolution,[status(thm)],[c_4,c_269])).

tff(c_623,plain,(
    ! [A_754] :
      ( v3_pre_topc(A_754,'#skF_4')
      | ~ v3_pre_topc(A_754,'#skF_2')
      | ~ m1_subset_1(A_754,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_754,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_615])).

tff(c_862,plain,(
    ! [A_777] :
      ( v3_pre_topc(A_777,'#skF_4')
      | ~ v3_pre_topc(A_777,'#skF_2')
      | ~ m1_subset_1(A_777,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_777,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_623])).

tff(c_891,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_862])).

tff(c_909,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_34,c_891])).

tff(c_32,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_235,plain,(
    ! [A_683] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_683,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_226])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_118,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_193,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_78])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_480,plain,(
    ! [B_721,D_723,E_722,A_724,C_725] :
      ( k3_tmap_1(A_724,B_721,C_725,D_723,E_722) = k2_partfun1(u1_struct_0(C_725),u1_struct_0(B_721),E_722,u1_struct_0(D_723))
      | ~ m1_pre_topc(D_723,C_725)
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_725),u1_struct_0(B_721))))
      | ~ v1_funct_2(E_722,u1_struct_0(C_725),u1_struct_0(B_721))
      | ~ v1_funct_1(E_722)
      | ~ m1_pre_topc(D_723,A_724)
      | ~ m1_pre_topc(C_725,A_724)
      | ~ l1_pre_topc(B_721)
      | ~ v2_pre_topc(B_721)
      | v2_struct_0(B_721)
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_482,plain,(
    ! [A_724,D_723] :
      ( k3_tmap_1(A_724,'#skF_1','#skF_4',D_723,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_723))
      | ~ m1_pre_topc(D_723,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_723,A_724)
      | ~ m1_pre_topc('#skF_4',A_724)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(resolution,[status(thm)],[c_44,c_480])).

tff(c_488,plain,(
    ! [A_724,D_723] :
      ( k3_tmap_1(A_724,'#skF_1','#skF_4',D_723,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_723))
      | ~ m1_pre_topc(D_723,'#skF_4')
      | ~ m1_pre_topc(D_723,A_724)
      | ~ m1_pre_topc('#skF_4',A_724)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_482])).

tff(c_736,plain,(
    ! [A_766,D_767] :
      ( k3_tmap_1(A_766,'#skF_1','#skF_4',D_767,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_767))
      | ~ m1_pre_topc(D_767,'#skF_4')
      | ~ m1_pre_topc(D_767,A_766)
      | ~ m1_pre_topc('#skF_4',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_488])).

tff(c_740,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_736])).

tff(c_750,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_740])).

tff(c_751,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_750])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_304])).

tff(c_119,plain,(
    ! [B_658,A_659] :
      ( v2_pre_topc(B_658)
      | ~ m1_pre_topc(B_658,A_659)
      | ~ l1_pre_topc(A_659)
      | ~ v2_pre_topc(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_137,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_128])).

tff(c_359,plain,(
    ! [A_703,B_704,C_705,D_706] :
      ( k2_partfun1(u1_struct_0(A_703),u1_struct_0(B_704),C_705,u1_struct_0(D_706)) = k2_tmap_1(A_703,B_704,C_705,D_706)
      | ~ m1_pre_topc(D_706,A_703)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703),u1_struct_0(B_704))))
      | ~ v1_funct_2(C_705,u1_struct_0(A_703),u1_struct_0(B_704))
      | ~ v1_funct_1(C_705)
      | ~ l1_pre_topc(B_704)
      | ~ v2_pre_topc(B_704)
      | v2_struct_0(B_704)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_361,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_706)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_706)
      | ~ m1_pre_topc(D_706,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_359])).

tff(c_367,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_706)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_706)
      | ~ m1_pre_topc(D_706,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_111,c_66,c_64,c_48,c_46,c_361])).

tff(c_368,plain,(
    ! [D_706] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_706)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_706)
      | ~ m1_pre_topc(D_706,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_367])).

tff(c_763,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_368])).

tff(c_770,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_763])).

tff(c_775,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_118])).

tff(c_797,plain,(
    ! [E_771,D_774,A_772,C_768,B_770,H_769,F_773] :
      ( r1_tmap_1(D_774,B_770,E_771,H_769)
      | ~ r1_tmap_1(C_768,B_770,k3_tmap_1(A_772,B_770,D_774,C_768,E_771),H_769)
      | ~ r1_tarski(F_773,u1_struct_0(C_768))
      | ~ r2_hidden(H_769,F_773)
      | ~ v3_pre_topc(F_773,D_774)
      | ~ m1_subset_1(H_769,u1_struct_0(C_768))
      | ~ m1_subset_1(H_769,u1_struct_0(D_774))
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0(D_774)))
      | ~ m1_pre_topc(C_768,D_774)
      | ~ m1_subset_1(E_771,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_774),u1_struct_0(B_770))))
      | ~ v1_funct_2(E_771,u1_struct_0(D_774),u1_struct_0(B_770))
      | ~ v1_funct_1(E_771)
      | ~ m1_pre_topc(D_774,A_772)
      | v2_struct_0(D_774)
      | ~ m1_pre_topc(C_768,A_772)
      | v2_struct_0(C_768)
      | ~ l1_pre_topc(B_770)
      | ~ v2_pre_topc(B_770)
      | v2_struct_0(B_770)
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772)
      | v2_struct_0(A_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_799,plain,(
    ! [H_769,F_773] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_769)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_769)
      | ~ r1_tarski(F_773,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_769,F_773)
      | ~ v3_pre_topc(F_773,'#skF_4')
      | ~ m1_subset_1(H_769,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_769,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(superposition,[status(thm),theory(equality)],[c_770,c_797])).

tff(c_801,plain,(
    ! [H_769,F_773] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_769)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_769)
      | ~ r1_tarski(F_773,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_769,F_773)
      | ~ v3_pre_topc(F_773,'#skF_4')
      | ~ m1_subset_1(H_769,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_769,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_773,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_54,c_50,c_48,c_46,c_44,c_42,c_799])).

tff(c_1010,plain,(
    ! [H_790,F_791] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5',H_790)
      | ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),H_790)
      | ~ r1_tarski(F_791,u1_struct_0('#skF_3'))
      | ~ r2_hidden(H_790,F_791)
      | ~ v3_pre_topc(F_791,'#skF_4')
      | ~ m1_subset_1(H_790,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_790,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_791,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_56,c_52,c_801])).

tff(c_1012,plain,(
    ! [F_791] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_791,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_791)
      | ~ v3_pre_topc(F_791,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_791,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_775,c_1010])).

tff(c_1018,plain,(
    ! [F_791] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_791,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_791)
      | ~ v3_pre_topc(F_791,'#skF_4')
      | ~ m1_subset_1(F_791,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_36,c_1012])).

tff(c_1061,plain,(
    ! [F_795] :
      ( ~ r1_tarski(F_795,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_795)
      | ~ v3_pre_topc(F_795,'#skF_4')
      | ~ m1_subset_1(F_795,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_1018])).

tff(c_1099,plain,(
    ! [A_796] :
      ( ~ r2_hidden('#skF_8',A_796)
      | ~ v3_pre_topc(A_796,'#skF_4')
      | ~ r1_tarski(A_796,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_235,c_1061])).

tff(c_1110,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1099])).

tff(c_1120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_909,c_80,c_1110])).

tff(c_1121,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_1123,plain,(
    ! [B_797,A_798] :
      ( v2_pre_topc(B_797)
      | ~ m1_pre_topc(B_797,A_798)
      | ~ l1_pre_topc(A_798)
      | ~ v2_pre_topc(A_798) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1132,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1123])).

tff(c_1141,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1132])).

tff(c_1504,plain,(
    ! [D_869,A_867,B_870,F_866,C_868] :
      ( r1_tmap_1(D_869,A_867,k2_tmap_1(B_870,A_867,C_868,D_869),F_866)
      | ~ r1_tmap_1(B_870,A_867,C_868,F_866)
      | ~ m1_subset_1(F_866,u1_struct_0(D_869))
      | ~ m1_subset_1(F_866,u1_struct_0(B_870))
      | ~ m1_pre_topc(D_869,B_870)
      | v2_struct_0(D_869)
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_870),u1_struct_0(A_867))))
      | ~ v1_funct_2(C_868,u1_struct_0(B_870),u1_struct_0(A_867))
      | ~ v1_funct_1(C_868)
      | ~ l1_pre_topc(B_870)
      | ~ v2_pre_topc(B_870)
      | v2_struct_0(B_870)
      | ~ l1_pre_topc(A_867)
      | ~ v2_pre_topc(A_867)
      | v2_struct_0(A_867) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1506,plain,(
    ! [D_869,F_866] :
      ( r1_tmap_1(D_869,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_869),F_866)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_866)
      | ~ m1_subset_1(F_866,u1_struct_0(D_869))
      | ~ m1_subset_1(F_866,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_869,'#skF_4')
      | v2_struct_0(D_869)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1504])).

tff(c_1512,plain,(
    ! [D_869,F_866] :
      ( r1_tmap_1(D_869,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_869),F_866)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_866)
      | ~ m1_subset_1(F_866,u1_struct_0(D_869))
      | ~ m1_subset_1(F_866,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_869,'#skF_4')
      | v2_struct_0(D_869)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1141,c_111,c_48,c_46,c_1506])).

tff(c_1513,plain,(
    ! [D_869,F_866] :
      ( r1_tmap_1(D_869,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_869),F_866)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_866)
      | ~ m1_subset_1(F_866,u1_struct_0(D_869))
      | ~ m1_subset_1(F_866,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_869,'#skF_4')
      | v2_struct_0(D_869) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1512])).

tff(c_1406,plain,(
    ! [C_855,B_851,E_852,D_853,A_854] :
      ( k3_tmap_1(A_854,B_851,C_855,D_853,E_852) = k2_partfun1(u1_struct_0(C_855),u1_struct_0(B_851),E_852,u1_struct_0(D_853))
      | ~ m1_pre_topc(D_853,C_855)
      | ~ m1_subset_1(E_852,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_855),u1_struct_0(B_851))))
      | ~ v1_funct_2(E_852,u1_struct_0(C_855),u1_struct_0(B_851))
      | ~ v1_funct_1(E_852)
      | ~ m1_pre_topc(D_853,A_854)
      | ~ m1_pre_topc(C_855,A_854)
      | ~ l1_pre_topc(B_851)
      | ~ v2_pre_topc(B_851)
      | v2_struct_0(B_851)
      | ~ l1_pre_topc(A_854)
      | ~ v2_pre_topc(A_854)
      | v2_struct_0(A_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1408,plain,(
    ! [A_854,D_853] :
      ( k3_tmap_1(A_854,'#skF_1','#skF_4',D_853,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_853))
      | ~ m1_pre_topc(D_853,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_853,A_854)
      | ~ m1_pre_topc('#skF_4',A_854)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_854)
      | ~ v2_pre_topc(A_854)
      | v2_struct_0(A_854) ) ),
    inference(resolution,[status(thm)],[c_44,c_1406])).

tff(c_1414,plain,(
    ! [A_854,D_853] :
      ( k3_tmap_1(A_854,'#skF_1','#skF_4',D_853,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_853))
      | ~ m1_pre_topc(D_853,'#skF_4')
      | ~ m1_pre_topc(D_853,A_854)
      | ~ m1_pre_topc('#skF_4',A_854)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_854)
      | ~ v2_pre_topc(A_854)
      | v2_struct_0(A_854) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_1408])).

tff(c_1686,plain,(
    ! [A_904,D_905] :
      ( k3_tmap_1(A_904,'#skF_1','#skF_4',D_905,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_905))
      | ~ m1_pre_topc(D_905,'#skF_4')
      | ~ m1_pre_topc(D_905,A_904)
      | ~ m1_pre_topc('#skF_4',A_904)
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904)
      | v2_struct_0(A_904) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1414])).

tff(c_1690,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1686])).

tff(c_1700,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_42,c_1690])).

tff(c_1701,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1700])).

tff(c_1324,plain,(
    ! [A_834,B_835,C_836,D_837] :
      ( k2_partfun1(u1_struct_0(A_834),u1_struct_0(B_835),C_836,u1_struct_0(D_837)) = k2_tmap_1(A_834,B_835,C_836,D_837)
      | ~ m1_pre_topc(D_837,A_834)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834),u1_struct_0(B_835))))
      | ~ v1_funct_2(C_836,u1_struct_0(A_834),u1_struct_0(B_835))
      | ~ v1_funct_1(C_836)
      | ~ l1_pre_topc(B_835)
      | ~ v2_pre_topc(B_835)
      | v2_struct_0(B_835)
      | ~ l1_pre_topc(A_834)
      | ~ v2_pre_topc(A_834)
      | v2_struct_0(A_834) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1326,plain,(
    ! [D_837] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_837)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_837)
      | ~ m1_pre_topc(D_837,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1324])).

tff(c_1332,plain,(
    ! [D_837] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_837)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_837)
      | ~ m1_pre_topc(D_837,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_111,c_66,c_64,c_48,c_46,c_1326])).

tff(c_1333,plain,(
    ! [D_837] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_837)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_837)
      | ~ m1_pre_topc(D_837,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_1332])).

tff(c_1767,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_1333])).

tff(c_1774,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1767])).

tff(c_1143,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_78])).

tff(c_1779,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1143])).

tff(c_1791,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1513,c_1779])).

tff(c_1794,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_79,c_36,c_1121,c_1791])).

tff(c_1796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.89  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.80/1.89  
% 4.80/1.89  %Foreground sorts:
% 4.80/1.89  
% 4.80/1.89  
% 4.80/1.89  %Background operators:
% 4.80/1.89  
% 4.80/1.89  
% 4.80/1.89  %Foreground operators:
% 4.80/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.80/1.89  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.80/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.80/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.89  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.80/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.80/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.80/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.80/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.80/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.80/1.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.80/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.80/1.89  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.80/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.89  
% 5.17/1.92  tff(f_304, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 5.17/1.92  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.17/1.92  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.17/1.92  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.17/1.92  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 5.17/1.92  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.17/1.92  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.17/1.92  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.17/1.92  tff(f_246, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 5.17/1.92  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.17/1.92  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_28, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_79, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 5.17/1.92  tff(c_36, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_95, plain, (![B_656, A_657]: (l1_pre_topc(B_656) | ~m1_pre_topc(B_656, A_657) | ~l1_pre_topc(A_657))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/1.92  tff(c_104, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_95])).
% 5.17/1.92  tff(c_111, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_104])).
% 5.17/1.92  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/1.92  tff(c_194, plain, (![C_675, A_676, B_677]: (m1_subset_1(C_675, k1_zfmisc_1(u1_struct_0(A_676))) | ~m1_subset_1(C_675, k1_zfmisc_1(u1_struct_0(B_677))) | ~m1_pre_topc(B_677, A_676) | ~l1_pre_topc(A_676))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.17/1.92  tff(c_220, plain, (![A_683, A_684, B_685]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0(A_684))) | ~m1_pre_topc(B_685, A_684) | ~l1_pre_topc(A_684) | ~r1_tarski(A_683, u1_struct_0(B_685)))), inference(resolution, [status(thm)], [c_4, c_194])).
% 5.17/1.92  tff(c_226, plain, (![A_683]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_683, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_220])).
% 5.17/1.92  tff(c_258, plain, (![A_688]: (m1_subset_1(A_688, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_688, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_226])).
% 5.17/1.92  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/1.92  tff(c_287, plain, (![A_692]: (r1_tarski(A_692, u1_struct_0('#skF_4')) | ~r1_tarski(A_692, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_258, c_2])).
% 5.17/1.92  tff(c_298, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_287])).
% 5.17/1.92  tff(c_34, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_269, plain, (![D_689, C_690, A_691]: (v3_pre_topc(D_689, C_690) | ~m1_subset_1(D_689, k1_zfmisc_1(u1_struct_0(C_690))) | ~v3_pre_topc(D_689, A_691) | ~m1_pre_topc(C_690, A_691) | ~m1_subset_1(D_689, k1_zfmisc_1(u1_struct_0(A_691))) | ~l1_pre_topc(A_691))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.17/1.92  tff(c_615, plain, (![A_754, C_755, A_756]: (v3_pre_topc(A_754, C_755) | ~v3_pre_topc(A_754, A_756) | ~m1_pre_topc(C_755, A_756) | ~m1_subset_1(A_754, k1_zfmisc_1(u1_struct_0(A_756))) | ~l1_pre_topc(A_756) | ~r1_tarski(A_754, u1_struct_0(C_755)))), inference(resolution, [status(thm)], [c_4, c_269])).
% 5.17/1.92  tff(c_623, plain, (![A_754]: (v3_pre_topc(A_754, '#skF_4') | ~v3_pre_topc(A_754, '#skF_2') | ~m1_subset_1(A_754, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_754, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_615])).
% 5.17/1.92  tff(c_862, plain, (![A_777]: (v3_pre_topc(A_777, '#skF_4') | ~v3_pre_topc(A_777, '#skF_2') | ~m1_subset_1(A_777, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_777, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_623])).
% 5.17/1.92  tff(c_891, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_862])).
% 5.17/1.92  tff(c_909, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_34, c_891])).
% 5.17/1.92  tff(c_32, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 5.17/1.92  tff(c_235, plain, (![A_683]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_683, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_226])).
% 5.17/1.92  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_76])).
% 5.17/1.92  tff(c_118, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_77])).
% 5.17/1.92  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 5.17/1.92  tff(c_193, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_78])).
% 5.17/1.92  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_480, plain, (![B_721, D_723, E_722, A_724, C_725]: (k3_tmap_1(A_724, B_721, C_725, D_723, E_722)=k2_partfun1(u1_struct_0(C_725), u1_struct_0(B_721), E_722, u1_struct_0(D_723)) | ~m1_pre_topc(D_723, C_725) | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_725), u1_struct_0(B_721)))) | ~v1_funct_2(E_722, u1_struct_0(C_725), u1_struct_0(B_721)) | ~v1_funct_1(E_722) | ~m1_pre_topc(D_723, A_724) | ~m1_pre_topc(C_725, A_724) | ~l1_pre_topc(B_721) | ~v2_pre_topc(B_721) | v2_struct_0(B_721) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.17/1.92  tff(c_482, plain, (![A_724, D_723]: (k3_tmap_1(A_724, '#skF_1', '#skF_4', D_723, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_723)) | ~m1_pre_topc(D_723, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_723, A_724) | ~m1_pre_topc('#skF_4', A_724) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(resolution, [status(thm)], [c_44, c_480])).
% 5.17/1.92  tff(c_488, plain, (![A_724, D_723]: (k3_tmap_1(A_724, '#skF_1', '#skF_4', D_723, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_723)) | ~m1_pre_topc(D_723, '#skF_4') | ~m1_pre_topc(D_723, A_724) | ~m1_pre_topc('#skF_4', A_724) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_482])).
% 5.17/1.92  tff(c_736, plain, (![A_766, D_767]: (k3_tmap_1(A_766, '#skF_1', '#skF_4', D_767, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_767)) | ~m1_pre_topc(D_767, '#skF_4') | ~m1_pre_topc(D_767, A_766) | ~m1_pre_topc('#skF_4', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_68, c_488])).
% 5.17/1.92  tff(c_740, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_736])).
% 5.17/1.92  tff(c_750, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_740])).
% 5.17/1.92  tff(c_751, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_750])).
% 5.17/1.92  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_304])).
% 5.17/1.92  tff(c_119, plain, (![B_658, A_659]: (v2_pre_topc(B_658) | ~m1_pre_topc(B_658, A_659) | ~l1_pre_topc(A_659) | ~v2_pre_topc(A_659))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.17/1.92  tff(c_128, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_119])).
% 5.17/1.92  tff(c_137, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_128])).
% 5.17/1.92  tff(c_359, plain, (![A_703, B_704, C_705, D_706]: (k2_partfun1(u1_struct_0(A_703), u1_struct_0(B_704), C_705, u1_struct_0(D_706))=k2_tmap_1(A_703, B_704, C_705, D_706) | ~m1_pre_topc(D_706, A_703) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703), u1_struct_0(B_704)))) | ~v1_funct_2(C_705, u1_struct_0(A_703), u1_struct_0(B_704)) | ~v1_funct_1(C_705) | ~l1_pre_topc(B_704) | ~v2_pre_topc(B_704) | v2_struct_0(B_704) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.17/1.92  tff(c_361, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_706))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_706) | ~m1_pre_topc(D_706, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_359])).
% 5.17/1.92  tff(c_367, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_706))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_706) | ~m1_pre_topc(D_706, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_111, c_66, c_64, c_48, c_46, c_361])).
% 5.17/1.92  tff(c_368, plain, (![D_706]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_706))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_706) | ~m1_pre_topc(D_706, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_367])).
% 5.17/1.92  tff(c_763, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_751, c_368])).
% 5.17/1.92  tff(c_770, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_763])).
% 5.17/1.92  tff(c_775, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_770, c_118])).
% 5.17/1.92  tff(c_797, plain, (![E_771, D_774, A_772, C_768, B_770, H_769, F_773]: (r1_tmap_1(D_774, B_770, E_771, H_769) | ~r1_tmap_1(C_768, B_770, k3_tmap_1(A_772, B_770, D_774, C_768, E_771), H_769) | ~r1_tarski(F_773, u1_struct_0(C_768)) | ~r2_hidden(H_769, F_773) | ~v3_pre_topc(F_773, D_774) | ~m1_subset_1(H_769, u1_struct_0(C_768)) | ~m1_subset_1(H_769, u1_struct_0(D_774)) | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0(D_774))) | ~m1_pre_topc(C_768, D_774) | ~m1_subset_1(E_771, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_774), u1_struct_0(B_770)))) | ~v1_funct_2(E_771, u1_struct_0(D_774), u1_struct_0(B_770)) | ~v1_funct_1(E_771) | ~m1_pre_topc(D_774, A_772) | v2_struct_0(D_774) | ~m1_pre_topc(C_768, A_772) | v2_struct_0(C_768) | ~l1_pre_topc(B_770) | ~v2_pre_topc(B_770) | v2_struct_0(B_770) | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772) | v2_struct_0(A_772))), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.17/1.92  tff(c_799, plain, (![H_769, F_773]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_769) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_769) | ~r1_tarski(F_773, u1_struct_0('#skF_3')) | ~r2_hidden(H_769, F_773) | ~v3_pre_topc(F_773, '#skF_4') | ~m1_subset_1(H_769, u1_struct_0('#skF_3')) | ~m1_subset_1(H_769, u1_struct_0('#skF_4')) | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_770, c_797])).
% 5.17/1.92  tff(c_801, plain, (![H_769, F_773]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_769) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_769) | ~r1_tarski(F_773, u1_struct_0('#skF_3')) | ~r2_hidden(H_769, F_773) | ~v3_pre_topc(F_773, '#skF_4') | ~m1_subset_1(H_769, u1_struct_0('#skF_3')) | ~m1_subset_1(H_769, u1_struct_0('#skF_4')) | ~m1_subset_1(F_773, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_66, c_64, c_54, c_50, c_48, c_46, c_44, c_42, c_799])).
% 5.17/1.92  tff(c_1010, plain, (![H_790, F_791]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', H_790) | ~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), H_790) | ~r1_tarski(F_791, u1_struct_0('#skF_3')) | ~r2_hidden(H_790, F_791) | ~v3_pre_topc(F_791, '#skF_4') | ~m1_subset_1(H_790, u1_struct_0('#skF_3')) | ~m1_subset_1(H_790, u1_struct_0('#skF_4')) | ~m1_subset_1(F_791, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_56, c_52, c_801])).
% 5.17/1.92  tff(c_1012, plain, (![F_791]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_791, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_791) | ~v3_pre_topc(F_791, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_791, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_775, c_1010])).
% 5.17/1.92  tff(c_1018, plain, (![F_791]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_791, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_791) | ~v3_pre_topc(F_791, '#skF_4') | ~m1_subset_1(F_791, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_36, c_1012])).
% 5.17/1.92  tff(c_1061, plain, (![F_795]: (~r1_tarski(F_795, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_795) | ~v3_pre_topc(F_795, '#skF_4') | ~m1_subset_1(F_795, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_193, c_1018])).
% 5.17/1.92  tff(c_1099, plain, (![A_796]: (~r2_hidden('#skF_8', A_796) | ~v3_pre_topc(A_796, '#skF_4') | ~r1_tarski(A_796, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_235, c_1061])).
% 5.17/1.92  tff(c_1110, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_1099])).
% 5.17/1.92  tff(c_1120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_909, c_80, c_1110])).
% 5.17/1.92  tff(c_1121, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_77])).
% 5.17/1.92  tff(c_1123, plain, (![B_797, A_798]: (v2_pre_topc(B_797) | ~m1_pre_topc(B_797, A_798) | ~l1_pre_topc(A_798) | ~v2_pre_topc(A_798))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.17/1.92  tff(c_1132, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1123])).
% 5.17/1.92  tff(c_1141, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1132])).
% 5.17/1.92  tff(c_1504, plain, (![D_869, A_867, B_870, F_866, C_868]: (r1_tmap_1(D_869, A_867, k2_tmap_1(B_870, A_867, C_868, D_869), F_866) | ~r1_tmap_1(B_870, A_867, C_868, F_866) | ~m1_subset_1(F_866, u1_struct_0(D_869)) | ~m1_subset_1(F_866, u1_struct_0(B_870)) | ~m1_pre_topc(D_869, B_870) | v2_struct_0(D_869) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_870), u1_struct_0(A_867)))) | ~v1_funct_2(C_868, u1_struct_0(B_870), u1_struct_0(A_867)) | ~v1_funct_1(C_868) | ~l1_pre_topc(B_870) | ~v2_pre_topc(B_870) | v2_struct_0(B_870) | ~l1_pre_topc(A_867) | ~v2_pre_topc(A_867) | v2_struct_0(A_867))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.17/1.92  tff(c_1506, plain, (![D_869, F_866]: (r1_tmap_1(D_869, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_869), F_866) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_866) | ~m1_subset_1(F_866, u1_struct_0(D_869)) | ~m1_subset_1(F_866, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_869, '#skF_4') | v2_struct_0(D_869) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1504])).
% 5.17/1.92  tff(c_1512, plain, (![D_869, F_866]: (r1_tmap_1(D_869, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_869), F_866) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_866) | ~m1_subset_1(F_866, u1_struct_0(D_869)) | ~m1_subset_1(F_866, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_869, '#skF_4') | v2_struct_0(D_869) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1141, c_111, c_48, c_46, c_1506])).
% 5.17/1.92  tff(c_1513, plain, (![D_869, F_866]: (r1_tmap_1(D_869, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_869), F_866) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_866) | ~m1_subset_1(F_866, u1_struct_0(D_869)) | ~m1_subset_1(F_866, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_869, '#skF_4') | v2_struct_0(D_869))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1512])).
% 5.17/1.92  tff(c_1406, plain, (![C_855, B_851, E_852, D_853, A_854]: (k3_tmap_1(A_854, B_851, C_855, D_853, E_852)=k2_partfun1(u1_struct_0(C_855), u1_struct_0(B_851), E_852, u1_struct_0(D_853)) | ~m1_pre_topc(D_853, C_855) | ~m1_subset_1(E_852, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_855), u1_struct_0(B_851)))) | ~v1_funct_2(E_852, u1_struct_0(C_855), u1_struct_0(B_851)) | ~v1_funct_1(E_852) | ~m1_pre_topc(D_853, A_854) | ~m1_pre_topc(C_855, A_854) | ~l1_pre_topc(B_851) | ~v2_pre_topc(B_851) | v2_struct_0(B_851) | ~l1_pre_topc(A_854) | ~v2_pre_topc(A_854) | v2_struct_0(A_854))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.17/1.92  tff(c_1408, plain, (![A_854, D_853]: (k3_tmap_1(A_854, '#skF_1', '#skF_4', D_853, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_853)) | ~m1_pre_topc(D_853, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_853, A_854) | ~m1_pre_topc('#skF_4', A_854) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_854) | ~v2_pre_topc(A_854) | v2_struct_0(A_854))), inference(resolution, [status(thm)], [c_44, c_1406])).
% 5.17/1.92  tff(c_1414, plain, (![A_854, D_853]: (k3_tmap_1(A_854, '#skF_1', '#skF_4', D_853, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_853)) | ~m1_pre_topc(D_853, '#skF_4') | ~m1_pre_topc(D_853, A_854) | ~m1_pre_topc('#skF_4', A_854) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_854) | ~v2_pre_topc(A_854) | v2_struct_0(A_854))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_1408])).
% 5.17/1.92  tff(c_1686, plain, (![A_904, D_905]: (k3_tmap_1(A_904, '#skF_1', '#skF_4', D_905, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_905)) | ~m1_pre_topc(D_905, '#skF_4') | ~m1_pre_topc(D_905, A_904) | ~m1_pre_topc('#skF_4', A_904) | ~l1_pre_topc(A_904) | ~v2_pre_topc(A_904) | v2_struct_0(A_904))), inference(negUnitSimplification, [status(thm)], [c_68, c_1414])).
% 5.17/1.92  tff(c_1690, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1686])).
% 5.17/1.92  tff(c_1700, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_42, c_1690])).
% 5.17/1.92  tff(c_1701, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1700])).
% 5.17/1.92  tff(c_1324, plain, (![A_834, B_835, C_836, D_837]: (k2_partfun1(u1_struct_0(A_834), u1_struct_0(B_835), C_836, u1_struct_0(D_837))=k2_tmap_1(A_834, B_835, C_836, D_837) | ~m1_pre_topc(D_837, A_834) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_834), u1_struct_0(B_835)))) | ~v1_funct_2(C_836, u1_struct_0(A_834), u1_struct_0(B_835)) | ~v1_funct_1(C_836) | ~l1_pre_topc(B_835) | ~v2_pre_topc(B_835) | v2_struct_0(B_835) | ~l1_pre_topc(A_834) | ~v2_pre_topc(A_834) | v2_struct_0(A_834))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.17/1.92  tff(c_1326, plain, (![D_837]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_837))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_837) | ~m1_pre_topc(D_837, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1324])).
% 5.17/1.92  tff(c_1332, plain, (![D_837]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_837))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_837) | ~m1_pre_topc(D_837, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_111, c_66, c_64, c_48, c_46, c_1326])).
% 5.17/1.92  tff(c_1333, plain, (![D_837]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_837))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_837) | ~m1_pre_topc(D_837, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_1332])).
% 5.17/1.92  tff(c_1767, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1701, c_1333])).
% 5.17/1.92  tff(c_1774, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1767])).
% 5.17/1.92  tff(c_1143, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_78])).
% 5.17/1.92  tff(c_1779, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1143])).
% 5.17/1.92  tff(c_1791, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1513, c_1779])).
% 5.17/1.92  tff(c_1794, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_79, c_36, c_1121, c_1791])).
% 5.17/1.92  tff(c_1796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1794])).
% 5.17/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.92  
% 5.17/1.92  Inference rules
% 5.17/1.92  ----------------------
% 5.17/1.92  #Ref     : 0
% 5.17/1.92  #Sup     : 334
% 5.17/1.92  #Fact    : 0
% 5.17/1.92  #Define  : 0
% 5.17/1.92  #Split   : 4
% 5.17/1.92  #Chain   : 0
% 5.17/1.92  #Close   : 0
% 5.17/1.92  
% 5.17/1.92  Ordering : KBO
% 5.17/1.92  
% 5.17/1.92  Simplification rules
% 5.17/1.92  ----------------------
% 5.17/1.92  #Subsume      : 87
% 5.17/1.92  #Demod        : 400
% 5.17/1.92  #Tautology    : 78
% 5.17/1.92  #SimpNegUnit  : 31
% 5.17/1.92  #BackRed      : 4
% 5.17/1.92  
% 5.17/1.92  #Partial instantiations: 0
% 5.17/1.92  #Strategies tried      : 1
% 5.17/1.92  
% 5.17/1.93  Timing (in seconds)
% 5.17/1.93  ----------------------
% 5.17/1.93  Preprocessing        : 0.43
% 5.17/1.93  Parsing              : 0.22
% 5.17/1.93  CNF conversion       : 0.07
% 5.17/1.93  Main loop            : 0.69
% 5.17/1.93  Inferencing          : 0.26
% 5.17/1.93  Reduction            : 0.22
% 5.17/1.93  Demodulation         : 0.15
% 5.17/1.93  BG Simplification    : 0.03
% 5.17/1.93  Subsumption          : 0.14
% 5.17/1.93  Abstraction          : 0.03
% 5.17/1.93  MUC search           : 0.00
% 5.17/1.93  Cooper               : 0.00
% 5.17/1.93  Total                : 1.18
% 5.17/1.93  Index Insertion      : 0.00
% 5.17/1.93  Index Deletion       : 0.00
% 5.17/1.93  Index Matching       : 0.00
% 5.17/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
