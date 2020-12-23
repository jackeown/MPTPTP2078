%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:24 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 682 expanded)
%              Number of leaves         :   43 ( 273 expanded)
%              Depth                    :   18
%              Number of atoms          :  575 (5487 expanded)
%              Number of equality atoms :   34 ( 239 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_332,negated_conjecture,(
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
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_75,axiom,(
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

tff(f_274,axiom,(
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

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_42,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_93,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_44,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_46,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_159,plain,(
    ! [B_676,A_677] :
      ( v2_pre_topc(B_676)
      | ~ m1_pre_topc(B_676,A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_159])).

tff(c_177,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_168])).

tff(c_100,plain,(
    ! [B_664,A_665] :
      ( l1_pre_topc(B_664)
      | ~ m1_pre_topc(B_664,A_665)
      | ~ l1_pre_topc(A_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_100])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_554,plain,(
    ! [B_714,C_715,A_716] :
      ( m1_pre_topc(B_714,C_715)
      | ~ r1_tarski(u1_struct_0(B_714),u1_struct_0(C_715))
      | ~ m1_pre_topc(C_715,A_716)
      | ~ m1_pre_topc(B_714,A_716)
      | ~ l1_pre_topc(A_716)
      | ~ v2_pre_topc(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_577,plain,(
    ! [B_717,A_718] :
      ( m1_pre_topc(B_717,B_717)
      | ~ m1_pre_topc(B_717,A_718)
      | ~ l1_pre_topc(A_718)
      | ~ v2_pre_topc(A_718) ) ),
    inference(resolution,[status(thm)],[c_12,c_554])).

tff(c_585,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_577])).

tff(c_595,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_585])).

tff(c_30,plain,(
    ! [B_88,C_90,A_84] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0(C_90))
      | ~ m1_pre_topc(B_88,C_90)
      | ~ m1_pre_topc(C_90,A_84)
      | ~ m1_pre_topc(B_88,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_624,plain,(
    ! [B_88] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_88,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_595,c_30])).

tff(c_698,plain,(
    ! [B_720] :
      ( r1_tarski(u1_struct_0(B_720),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_720,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_116,c_624])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    ! [C_678,B_679,A_680] :
      ( r2_hidden(C_678,B_679)
      | ~ r2_hidden(C_678,A_680)
      | ~ r1_tarski(A_680,B_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_267,plain,(
    ! [A_692,B_693,B_694] :
      ( r2_hidden('#skF_1'(A_692,B_693),B_694)
      | ~ r1_tarski(A_692,B_694)
      | r1_tarski(A_692,B_693) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_274,plain,(
    ! [A_692,B_693,B_2,B_694] :
      ( r2_hidden('#skF_1'(A_692,B_693),B_2)
      | ~ r1_tarski(B_694,B_2)
      | ~ r1_tarski(A_692,B_694)
      | r1_tarski(A_692,B_693) ) ),
    inference(resolution,[status(thm)],[c_267,c_2])).

tff(c_2561,plain,(
    ! [A_905,B_906,B_907] :
      ( r2_hidden('#skF_1'(A_905,B_906),u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_905,u1_struct_0(B_907))
      | r1_tarski(A_905,B_906)
      | ~ m1_pre_topc(B_907,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_698,c_274])).

tff(c_2575,plain,(
    ! [B_906] :
      ( r2_hidden('#skF_1'('#skF_7',B_906),u1_struct_0('#skF_5'))
      | r1_tarski('#skF_7',B_906)
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_2561])).

tff(c_2605,plain,(
    ! [B_910] :
      ( r2_hidden('#skF_1'('#skF_7',B_910),u1_struct_0('#skF_5'))
      | r1_tarski('#skF_7',B_910) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2575])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2613,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2605,c_4])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_843,plain,(
    ! [B_728,A_729,C_730] :
      ( m1_connsp_2(B_728,A_729,C_730)
      | ~ r2_hidden(C_730,B_728)
      | ~ v3_pre_topc(B_728,A_729)
      | ~ m1_subset_1(C_730,u1_struct_0(A_729))
      | ~ m1_subset_1(B_728,k1_zfmisc_1(u1_struct_0(A_729)))
      | ~ l1_pre_topc(A_729)
      | ~ v2_pre_topc(A_729)
      | v2_struct_0(A_729) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_845,plain,(
    ! [B_728] :
      ( m1_connsp_2(B_728,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_728)
      | ~ v3_pre_topc(B_728,'#skF_5')
      | ~ m1_subset_1(B_728,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_843])).

tff(c_850,plain,(
    ! [B_728] :
      ( m1_connsp_2(B_728,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_728)
      | ~ v3_pre_topc(B_728,'#skF_5')
      | ~ m1_subset_1(B_728,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_116,c_845])).

tff(c_857,plain,(
    ! [B_731] :
      ( m1_connsp_2(B_731,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',B_731)
      | ~ v3_pre_topc(B_731,'#skF_5')
      | ~ m1_subset_1(B_731,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_850])).

tff(c_862,plain,(
    ! [A_8] :
      ( m1_connsp_2(A_8,'#skF_5','#skF_8')
      | ~ r2_hidden('#skF_8',A_8)
      | ~ v3_pre_topc(A_8,'#skF_5')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_857])).

tff(c_2624,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_2613,c_862])).

tff(c_2641,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2624])).

tff(c_2648,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2641])).

tff(c_48,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_745,plain,(
    ! [D_721,C_722,A_723] :
      ( v3_pre_topc(D_721,C_722)
      | ~ m1_subset_1(D_721,k1_zfmisc_1(u1_struct_0(C_722)))
      | ~ v3_pre_topc(D_721,A_723)
      | ~ m1_pre_topc(C_722,A_723)
      | ~ m1_subset_1(D_721,k1_zfmisc_1(u1_struct_0(A_723)))
      | ~ l1_pre_topc(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2649,plain,(
    ! [A_911,C_912,A_913] :
      ( v3_pre_topc(A_911,C_912)
      | ~ v3_pre_topc(A_911,A_913)
      | ~ m1_pre_topc(C_912,A_913)
      | ~ m1_subset_1(A_911,k1_zfmisc_1(u1_struct_0(A_913)))
      | ~ l1_pre_topc(A_913)
      | ~ r1_tarski(A_911,u1_struct_0(C_912)) ) ),
    inference(resolution,[status(thm)],[c_16,c_745])).

tff(c_2661,plain,(
    ! [A_911] :
      ( v3_pre_topc(A_911,'#skF_5')
      | ~ v3_pre_topc(A_911,'#skF_3')
      | ~ m1_subset_1(A_911,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_911,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_64,c_2649])).

tff(c_3007,plain,(
    ! [A_933] :
      ( v3_pre_topc(A_933,'#skF_5')
      | ~ v3_pre_topc(A_933,'#skF_3')
      | ~ m1_subset_1(A_933,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_933,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2661])).

tff(c_3014,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_3')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_3007])).

tff(c_3018,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2613,c_48,c_3014])).

tff(c_3020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2648,c_3018])).

tff(c_3021,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2641])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_92,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_84])).

tff(c_178,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_80,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_78,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_60,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_2041,plain,(
    ! [D_848,A_847,C_850,E_851,B_849] :
      ( k3_tmap_1(A_847,B_849,C_850,D_848,E_851) = k2_partfun1(u1_struct_0(C_850),u1_struct_0(B_849),E_851,u1_struct_0(D_848))
      | ~ m1_pre_topc(D_848,C_850)
      | ~ m1_subset_1(E_851,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_850),u1_struct_0(B_849))))
      | ~ v1_funct_2(E_851,u1_struct_0(C_850),u1_struct_0(B_849))
      | ~ v1_funct_1(E_851)
      | ~ m1_pre_topc(D_848,A_847)
      | ~ m1_pre_topc(C_850,A_847)
      | ~ l1_pre_topc(B_849)
      | ~ v2_pre_topc(B_849)
      | v2_struct_0(B_849)
      | ~ l1_pre_topc(A_847)
      | ~ v2_pre_topc(A_847)
      | v2_struct_0(A_847) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2043,plain,(
    ! [A_847,D_848] :
      ( k3_tmap_1(A_847,'#skF_2','#skF_5',D_848,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_848))
      | ~ m1_pre_topc(D_848,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_848,A_847)
      | ~ m1_pre_topc('#skF_5',A_847)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_847)
      | ~ v2_pre_topc(A_847)
      | v2_struct_0(A_847) ) ),
    inference(resolution,[status(thm)],[c_58,c_2041])).

tff(c_2049,plain,(
    ! [A_847,D_848] :
      ( k3_tmap_1(A_847,'#skF_2','#skF_5',D_848,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_848))
      | ~ m1_pre_topc(D_848,'#skF_5')
      | ~ m1_pre_topc(D_848,A_847)
      | ~ m1_pre_topc('#skF_5',A_847)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_847)
      | ~ v2_pre_topc(A_847)
      | v2_struct_0(A_847) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_60,c_2043])).

tff(c_2090,plain,(
    ! [A_857,D_858] :
      ( k3_tmap_1(A_857,'#skF_2','#skF_5',D_858,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_858))
      | ~ m1_pre_topc(D_858,'#skF_5')
      | ~ m1_pre_topc(D_858,A_857)
      | ~ m1_pre_topc('#skF_5',A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2049])).

tff(c_2098,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2090])).

tff(c_2116,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_56,c_2098])).

tff(c_2117,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2116])).

tff(c_940,plain,(
    ! [A_735,B_736,C_737,D_738] :
      ( k2_partfun1(u1_struct_0(A_735),u1_struct_0(B_736),C_737,u1_struct_0(D_738)) = k2_tmap_1(A_735,B_736,C_737,D_738)
      | ~ m1_pre_topc(D_738,A_735)
      | ~ m1_subset_1(C_737,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_735),u1_struct_0(B_736))))
      | ~ v1_funct_2(C_737,u1_struct_0(A_735),u1_struct_0(B_736))
      | ~ v1_funct_1(C_737)
      | ~ l1_pre_topc(B_736)
      | ~ v2_pre_topc(B_736)
      | v2_struct_0(B_736)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_942,plain,(
    ! [D_738] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_738)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_738)
      | ~ m1_pre_topc(D_738,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_940])).

tff(c_948,plain,(
    ! [D_738] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_738)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_738)
      | ~ m1_pre_topc(D_738,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_116,c_80,c_78,c_62,c_60,c_942])).

tff(c_949,plain,(
    ! [D_738] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_738)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_738)
      | ~ m1_pre_topc(D_738,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_948])).

tff(c_2284,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_949])).

tff(c_2291,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2284])).

tff(c_90,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_332])).

tff(c_91,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_90])).

tff(c_265,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_91])).

tff(c_2302,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_265])).

tff(c_2502,plain,(
    ! [H_895,A_898,C_896,F_897,E_900,D_899,B_901] :
      ( r1_tmap_1(D_899,B_901,E_900,H_895)
      | ~ r1_tmap_1(C_896,B_901,k3_tmap_1(A_898,B_901,D_899,C_896,E_900),H_895)
      | ~ m1_connsp_2(F_897,D_899,H_895)
      | ~ r1_tarski(F_897,u1_struct_0(C_896))
      | ~ m1_subset_1(H_895,u1_struct_0(C_896))
      | ~ m1_subset_1(H_895,u1_struct_0(D_899))
      | ~ m1_subset_1(F_897,k1_zfmisc_1(u1_struct_0(D_899)))
      | ~ m1_pre_topc(C_896,D_899)
      | ~ m1_subset_1(E_900,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_899),u1_struct_0(B_901))))
      | ~ v1_funct_2(E_900,u1_struct_0(D_899),u1_struct_0(B_901))
      | ~ v1_funct_1(E_900)
      | ~ m1_pre_topc(D_899,A_898)
      | v2_struct_0(D_899)
      | ~ m1_pre_topc(C_896,A_898)
      | v2_struct_0(C_896)
      | ~ l1_pre_topc(B_901)
      | ~ v2_pre_topc(B_901)
      | v2_struct_0(B_901)
      | ~ l1_pre_topc(A_898)
      | ~ v2_pre_topc(A_898)
      | v2_struct_0(A_898) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_2508,plain,(
    ! [H_895,F_897] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6',H_895)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),H_895)
      | ~ m1_connsp_2(F_897,'#skF_5',H_895)
      | ~ r1_tarski(F_897,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_895,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_895,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_897,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_2502])).

tff(c_2518,plain,(
    ! [H_895,F_897] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6',H_895)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),H_895)
      | ~ m1_connsp_2(F_897,'#skF_5',H_895)
      | ~ r1_tarski(F_897,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_895,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_895,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_897,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_80,c_78,c_68,c_64,c_62,c_60,c_58,c_56,c_2508])).

tff(c_3504,plain,(
    ! [H_966,F_967] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6',H_966)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),H_966)
      | ~ m1_connsp_2(F_967,'#skF_5',H_966)
      | ~ r1_tarski(F_967,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_966,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_966,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_967,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_82,c_70,c_66,c_2518])).

tff(c_3509,plain,(
    ! [F_967] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_967,'#skF_5','#skF_8')
      | ~ r1_tarski(F_967,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_967,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_2302,c_3504])).

tff(c_3516,plain,(
    ! [F_967] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_967,'#skF_5','#skF_8')
      | ~ r1_tarski(F_967,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_967,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_93,c_3509])).

tff(c_3518,plain,(
    ! [F_968] :
      ( ~ m1_connsp_2(F_968,'#skF_5','#skF_8')
      | ~ r1_tarski(F_968,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_968,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_3516])).

tff(c_3524,plain,(
    ! [A_969] :
      ( ~ m1_connsp_2(A_969,'#skF_5','#skF_8')
      | ~ r1_tarski(A_969,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_969,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_3518])).

tff(c_3530,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2613,c_3524])).

tff(c_3545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3021,c_3530])).

tff(c_3547,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_4422,plain,(
    ! [B_1050,F_1046,D_1047,A_1049,C_1048] :
      ( r1_tmap_1(D_1047,A_1049,k2_tmap_1(B_1050,A_1049,C_1048,D_1047),F_1046)
      | ~ r1_tmap_1(B_1050,A_1049,C_1048,F_1046)
      | ~ m1_subset_1(F_1046,u1_struct_0(D_1047))
      | ~ m1_subset_1(F_1046,u1_struct_0(B_1050))
      | ~ m1_pre_topc(D_1047,B_1050)
      | v2_struct_0(D_1047)
      | ~ m1_subset_1(C_1048,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1050),u1_struct_0(A_1049))))
      | ~ v1_funct_2(C_1048,u1_struct_0(B_1050),u1_struct_0(A_1049))
      | ~ v1_funct_1(C_1048)
      | ~ l1_pre_topc(B_1050)
      | ~ v2_pre_topc(B_1050)
      | v2_struct_0(B_1050)
      | ~ l1_pre_topc(A_1049)
      | ~ v2_pre_topc(A_1049)
      | v2_struct_0(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4424,plain,(
    ! [D_1047,F_1046] :
      ( r1_tmap_1(D_1047,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1047),F_1046)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1046)
      | ~ m1_subset_1(F_1046,u1_struct_0(D_1047))
      | ~ m1_subset_1(F_1046,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1047,'#skF_5')
      | v2_struct_0(D_1047)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_4422])).

tff(c_4430,plain,(
    ! [D_1047,F_1046] :
      ( r1_tmap_1(D_1047,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1047),F_1046)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1046)
      | ~ m1_subset_1(F_1046,u1_struct_0(D_1047))
      | ~ m1_subset_1(F_1046,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1047,'#skF_5')
      | v2_struct_0(D_1047)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_177,c_116,c_62,c_60,c_4424])).

tff(c_4431,plain,(
    ! [D_1047,F_1046] :
      ( r1_tmap_1(D_1047,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1047),F_1046)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_1046)
      | ~ m1_subset_1(F_1046,u1_struct_0(D_1047))
      | ~ m1_subset_1(F_1046,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_1047,'#skF_5')
      | v2_struct_0(D_1047) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_66,c_4430])).

tff(c_4255,plain,(
    ! [E_1035,B_1033,A_1031,D_1032,C_1034] :
      ( k3_tmap_1(A_1031,B_1033,C_1034,D_1032,E_1035) = k2_partfun1(u1_struct_0(C_1034),u1_struct_0(B_1033),E_1035,u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,C_1034)
      | ~ m1_subset_1(E_1035,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1034),u1_struct_0(B_1033))))
      | ~ v1_funct_2(E_1035,u1_struct_0(C_1034),u1_struct_0(B_1033))
      | ~ v1_funct_1(E_1035)
      | ~ m1_pre_topc(D_1032,A_1031)
      | ~ m1_pre_topc(C_1034,A_1031)
      | ~ l1_pre_topc(B_1033)
      | ~ v2_pre_topc(B_1033)
      | v2_struct_0(B_1033)
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4257,plain,(
    ! [A_1031,D_1032] :
      ( k3_tmap_1(A_1031,'#skF_2','#skF_5',D_1032,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_1032,A_1031)
      | ~ m1_pre_topc('#skF_5',A_1031)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(resolution,[status(thm)],[c_58,c_4255])).

tff(c_4263,plain,(
    ! [A_1031,D_1032] :
      ( k3_tmap_1(A_1031,'#skF_2','#skF_5',D_1032,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1032))
      | ~ m1_pre_topc(D_1032,'#skF_5')
      | ~ m1_pre_topc(D_1032,A_1031)
      | ~ m1_pre_topc('#skF_5',A_1031)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1031)
      | ~ v2_pre_topc(A_1031)
      | v2_struct_0(A_1031) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_62,c_60,c_4257])).

tff(c_4679,plain,(
    ! [A_1086,D_1087] :
      ( k3_tmap_1(A_1086,'#skF_2','#skF_5',D_1087,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1087))
      | ~ m1_pre_topc(D_1087,'#skF_5')
      | ~ m1_pre_topc(D_1087,A_1086)
      | ~ m1_pre_topc('#skF_5',A_1086)
      | ~ l1_pre_topc(A_1086)
      | ~ v2_pre_topc(A_1086)
      | v2_struct_0(A_1086) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4263])).

tff(c_4687,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4679])).

tff(c_4705,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_64,c_56,c_4687])).

tff(c_4706,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4705])).

tff(c_4174,plain,(
    ! [A_1023,B_1024,C_1025,D_1026] :
      ( k2_partfun1(u1_struct_0(A_1023),u1_struct_0(B_1024),C_1025,u1_struct_0(D_1026)) = k2_tmap_1(A_1023,B_1024,C_1025,D_1026)
      | ~ m1_pre_topc(D_1026,A_1023)
      | ~ m1_subset_1(C_1025,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1023),u1_struct_0(B_1024))))
      | ~ v1_funct_2(C_1025,u1_struct_0(A_1023),u1_struct_0(B_1024))
      | ~ v1_funct_1(C_1025)
      | ~ l1_pre_topc(B_1024)
      | ~ v2_pre_topc(B_1024)
      | v2_struct_0(B_1024)
      | ~ l1_pre_topc(A_1023)
      | ~ v2_pre_topc(A_1023)
      | v2_struct_0(A_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4176,plain,(
    ! [D_1026] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1026)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1026)
      | ~ m1_pre_topc(D_1026,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4174])).

tff(c_4182,plain,(
    ! [D_1026] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1026)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1026)
      | ~ m1_pre_topc(D_1026,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_116,c_80,c_78,c_62,c_60,c_4176])).

tff(c_4183,plain,(
    ! [D_1026] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_1026)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_1026)
      | ~ m1_pre_topc(D_1026,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_4182])).

tff(c_4806,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4706,c_4183])).

tff(c_4813,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4806])).

tff(c_3546,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_4818,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4813,c_3546])).

tff(c_4844,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4431,c_4818])).

tff(c_4847,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_93,c_3547,c_4844])).

tff(c_4849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.28  
% 6.47/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.28  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 6.47/2.28  
% 6.47/2.28  %Foreground sorts:
% 6.47/2.28  
% 6.47/2.28  
% 6.47/2.28  %Background operators:
% 6.47/2.28  
% 6.47/2.28  
% 6.47/2.28  %Foreground operators:
% 6.47/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.47/2.28  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.47/2.28  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.47/2.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.47/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.28  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.47/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.47/2.28  tff('#skF_7', type, '#skF_7': $i).
% 6.47/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.47/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.47/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.47/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.47/2.28  tff('#skF_9', type, '#skF_9': $i).
% 6.47/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.28  tff('#skF_8', type, '#skF_8': $i).
% 6.47/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.47/2.28  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.47/2.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.47/2.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.47/2.28  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.47/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.47/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.47/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.28  
% 6.82/2.31  tff(f_332, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 6.82/2.31  tff(f_51, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.82/2.31  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.82/2.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.82/2.31  tff(f_167, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.82/2.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.82/2.31  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.82/2.31  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 6.82/2.31  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 6.82/2.31  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 6.82/2.31  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.82/2.31  tff(f_274, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 6.82/2.31  tff(f_207, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 6.82/2.31  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_52, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_42, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_50, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_93, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 6.82/2.31  tff(c_44, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_159, plain, (![B_676, A_677]: (v2_pre_topc(B_676) | ~m1_pre_topc(B_676, A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.82/2.31  tff(c_168, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_159])).
% 6.82/2.31  tff(c_177, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_168])).
% 6.82/2.31  tff(c_100, plain, (![B_664, A_665]: (l1_pre_topc(B_664) | ~m1_pre_topc(B_664, A_665) | ~l1_pre_topc(A_665))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.82/2.31  tff(c_109, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_100])).
% 6.82/2.31  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109])).
% 6.82/2.31  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.82/2.31  tff(c_554, plain, (![B_714, C_715, A_716]: (m1_pre_topc(B_714, C_715) | ~r1_tarski(u1_struct_0(B_714), u1_struct_0(C_715)) | ~m1_pre_topc(C_715, A_716) | ~m1_pre_topc(B_714, A_716) | ~l1_pre_topc(A_716) | ~v2_pre_topc(A_716))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.82/2.31  tff(c_577, plain, (![B_717, A_718]: (m1_pre_topc(B_717, B_717) | ~m1_pre_topc(B_717, A_718) | ~l1_pre_topc(A_718) | ~v2_pre_topc(A_718))), inference(resolution, [status(thm)], [c_12, c_554])).
% 6.82/2.31  tff(c_585, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_577])).
% 6.82/2.31  tff(c_595, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_585])).
% 6.82/2.31  tff(c_30, plain, (![B_88, C_90, A_84]: (r1_tarski(u1_struct_0(B_88), u1_struct_0(C_90)) | ~m1_pre_topc(B_88, C_90) | ~m1_pre_topc(C_90, A_84) | ~m1_pre_topc(B_88, A_84) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_167])).
% 6.82/2.31  tff(c_624, plain, (![B_88]: (r1_tarski(u1_struct_0(B_88), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_88, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_595, c_30])).
% 6.82/2.31  tff(c_698, plain, (![B_720]: (r1_tarski(u1_struct_0(B_720), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_720, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_116, c_624])).
% 6.82/2.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.31  tff(c_181, plain, (![C_678, B_679, A_680]: (r2_hidden(C_678, B_679) | ~r2_hidden(C_678, A_680) | ~r1_tarski(A_680, B_679))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.31  tff(c_267, plain, (![A_692, B_693, B_694]: (r2_hidden('#skF_1'(A_692, B_693), B_694) | ~r1_tarski(A_692, B_694) | r1_tarski(A_692, B_693))), inference(resolution, [status(thm)], [c_6, c_181])).
% 6.82/2.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.31  tff(c_274, plain, (![A_692, B_693, B_2, B_694]: (r2_hidden('#skF_1'(A_692, B_693), B_2) | ~r1_tarski(B_694, B_2) | ~r1_tarski(A_692, B_694) | r1_tarski(A_692, B_693))), inference(resolution, [status(thm)], [c_267, c_2])).
% 6.82/2.31  tff(c_2561, plain, (![A_905, B_906, B_907]: (r2_hidden('#skF_1'(A_905, B_906), u1_struct_0('#skF_5')) | ~r1_tarski(A_905, u1_struct_0(B_907)) | r1_tarski(A_905, B_906) | ~m1_pre_topc(B_907, '#skF_5'))), inference(resolution, [status(thm)], [c_698, c_274])).
% 6.82/2.31  tff(c_2575, plain, (![B_906]: (r2_hidden('#skF_1'('#skF_7', B_906), u1_struct_0('#skF_5')) | r1_tarski('#skF_7', B_906) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_2561])).
% 6.82/2.31  tff(c_2605, plain, (![B_910]: (r2_hidden('#skF_1'('#skF_7', B_910), u1_struct_0('#skF_5')) | r1_tarski('#skF_7', B_910))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2575])).
% 6.82/2.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.82/2.31  tff(c_2613, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2605, c_4])).
% 6.82/2.31  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.82/2.31  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_843, plain, (![B_728, A_729, C_730]: (m1_connsp_2(B_728, A_729, C_730) | ~r2_hidden(C_730, B_728) | ~v3_pre_topc(B_728, A_729) | ~m1_subset_1(C_730, u1_struct_0(A_729)) | ~m1_subset_1(B_728, k1_zfmisc_1(u1_struct_0(A_729))) | ~l1_pre_topc(A_729) | ~v2_pre_topc(A_729) | v2_struct_0(A_729))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.82/2.31  tff(c_845, plain, (![B_728]: (m1_connsp_2(B_728, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_728) | ~v3_pre_topc(B_728, '#skF_5') | ~m1_subset_1(B_728, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_843])).
% 6.82/2.31  tff(c_850, plain, (![B_728]: (m1_connsp_2(B_728, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_728) | ~v3_pre_topc(B_728, '#skF_5') | ~m1_subset_1(B_728, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_116, c_845])).
% 6.82/2.31  tff(c_857, plain, (![B_731]: (m1_connsp_2(B_731, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', B_731) | ~v3_pre_topc(B_731, '#skF_5') | ~m1_subset_1(B_731, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_850])).
% 6.82/2.31  tff(c_862, plain, (![A_8]: (m1_connsp_2(A_8, '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', A_8) | ~v3_pre_topc(A_8, '#skF_5') | ~r1_tarski(A_8, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_857])).
% 6.82/2.31  tff(c_2624, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_2613, c_862])).
% 6.82/2.31  tff(c_2641, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2624])).
% 6.82/2.31  tff(c_2648, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2641])).
% 6.82/2.31  tff(c_48, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_745, plain, (![D_721, C_722, A_723]: (v3_pre_topc(D_721, C_722) | ~m1_subset_1(D_721, k1_zfmisc_1(u1_struct_0(C_722))) | ~v3_pre_topc(D_721, A_723) | ~m1_pre_topc(C_722, A_723) | ~m1_subset_1(D_721, k1_zfmisc_1(u1_struct_0(A_723))) | ~l1_pre_topc(A_723))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.82/2.31  tff(c_2649, plain, (![A_911, C_912, A_913]: (v3_pre_topc(A_911, C_912) | ~v3_pre_topc(A_911, A_913) | ~m1_pre_topc(C_912, A_913) | ~m1_subset_1(A_911, k1_zfmisc_1(u1_struct_0(A_913))) | ~l1_pre_topc(A_913) | ~r1_tarski(A_911, u1_struct_0(C_912)))), inference(resolution, [status(thm)], [c_16, c_745])).
% 6.82/2.31  tff(c_2661, plain, (![A_911]: (v3_pre_topc(A_911, '#skF_5') | ~v3_pre_topc(A_911, '#skF_3') | ~m1_subset_1(A_911, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_911, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_64, c_2649])).
% 6.82/2.31  tff(c_3007, plain, (![A_933]: (v3_pre_topc(A_933, '#skF_5') | ~v3_pre_topc(A_933, '#skF_3') | ~m1_subset_1(A_933, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_933, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2661])).
% 6.82/2.31  tff(c_3014, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_3007])).
% 6.82/2.31  tff(c_3018, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2613, c_48, c_3014])).
% 6.82/2.31  tff(c_3020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2648, c_3018])).
% 6.82/2.31  tff(c_3021, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_2641])).
% 6.82/2.31  tff(c_84, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_92, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_84])).
% 6.82/2.31  tff(c_178, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_92])).
% 6.82/2.31  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_82, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_80, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_78, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_60, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_2041, plain, (![D_848, A_847, C_850, E_851, B_849]: (k3_tmap_1(A_847, B_849, C_850, D_848, E_851)=k2_partfun1(u1_struct_0(C_850), u1_struct_0(B_849), E_851, u1_struct_0(D_848)) | ~m1_pre_topc(D_848, C_850) | ~m1_subset_1(E_851, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_850), u1_struct_0(B_849)))) | ~v1_funct_2(E_851, u1_struct_0(C_850), u1_struct_0(B_849)) | ~v1_funct_1(E_851) | ~m1_pre_topc(D_848, A_847) | ~m1_pre_topc(C_850, A_847) | ~l1_pre_topc(B_849) | ~v2_pre_topc(B_849) | v2_struct_0(B_849) | ~l1_pre_topc(A_847) | ~v2_pre_topc(A_847) | v2_struct_0(A_847))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.82/2.31  tff(c_2043, plain, (![A_847, D_848]: (k3_tmap_1(A_847, '#skF_2', '#skF_5', D_848, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_848)) | ~m1_pre_topc(D_848, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_848, A_847) | ~m1_pre_topc('#skF_5', A_847) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_847) | ~v2_pre_topc(A_847) | v2_struct_0(A_847))), inference(resolution, [status(thm)], [c_58, c_2041])).
% 6.82/2.31  tff(c_2049, plain, (![A_847, D_848]: (k3_tmap_1(A_847, '#skF_2', '#skF_5', D_848, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_848)) | ~m1_pre_topc(D_848, '#skF_5') | ~m1_pre_topc(D_848, A_847) | ~m1_pre_topc('#skF_5', A_847) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_847) | ~v2_pre_topc(A_847) | v2_struct_0(A_847))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_60, c_2043])).
% 6.82/2.31  tff(c_2090, plain, (![A_857, D_858]: (k3_tmap_1(A_857, '#skF_2', '#skF_5', D_858, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_858)) | ~m1_pre_topc(D_858, '#skF_5') | ~m1_pre_topc(D_858, A_857) | ~m1_pre_topc('#skF_5', A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857))), inference(negUnitSimplification, [status(thm)], [c_82, c_2049])).
% 6.82/2.31  tff(c_2098, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2090])).
% 6.82/2.31  tff(c_2116, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_56, c_2098])).
% 6.82/2.31  tff(c_2117, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_2116])).
% 6.82/2.31  tff(c_940, plain, (![A_735, B_736, C_737, D_738]: (k2_partfun1(u1_struct_0(A_735), u1_struct_0(B_736), C_737, u1_struct_0(D_738))=k2_tmap_1(A_735, B_736, C_737, D_738) | ~m1_pre_topc(D_738, A_735) | ~m1_subset_1(C_737, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_735), u1_struct_0(B_736)))) | ~v1_funct_2(C_737, u1_struct_0(A_735), u1_struct_0(B_736)) | ~v1_funct_1(C_737) | ~l1_pre_topc(B_736) | ~v2_pre_topc(B_736) | v2_struct_0(B_736) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.82/2.31  tff(c_942, plain, (![D_738]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_738))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_738) | ~m1_pre_topc(D_738, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_940])).
% 6.82/2.31  tff(c_948, plain, (![D_738]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_738))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_738) | ~m1_pre_topc(D_738, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_116, c_80, c_78, c_62, c_60, c_942])).
% 6.82/2.31  tff(c_949, plain, (![D_738]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_738))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_738) | ~m1_pre_topc(D_738, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_948])).
% 6.82/2.31  tff(c_2284, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2117, c_949])).
% 6.82/2.31  tff(c_2291, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2284])).
% 6.82/2.31  tff(c_90, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_332])).
% 6.82/2.31  tff(c_91, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_90])).
% 6.82/2.31  tff(c_265, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_178, c_91])).
% 6.82/2.31  tff(c_2302, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2291, c_265])).
% 6.82/2.31  tff(c_2502, plain, (![H_895, A_898, C_896, F_897, E_900, D_899, B_901]: (r1_tmap_1(D_899, B_901, E_900, H_895) | ~r1_tmap_1(C_896, B_901, k3_tmap_1(A_898, B_901, D_899, C_896, E_900), H_895) | ~m1_connsp_2(F_897, D_899, H_895) | ~r1_tarski(F_897, u1_struct_0(C_896)) | ~m1_subset_1(H_895, u1_struct_0(C_896)) | ~m1_subset_1(H_895, u1_struct_0(D_899)) | ~m1_subset_1(F_897, k1_zfmisc_1(u1_struct_0(D_899))) | ~m1_pre_topc(C_896, D_899) | ~m1_subset_1(E_900, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_899), u1_struct_0(B_901)))) | ~v1_funct_2(E_900, u1_struct_0(D_899), u1_struct_0(B_901)) | ~v1_funct_1(E_900) | ~m1_pre_topc(D_899, A_898) | v2_struct_0(D_899) | ~m1_pre_topc(C_896, A_898) | v2_struct_0(C_896) | ~l1_pre_topc(B_901) | ~v2_pre_topc(B_901) | v2_struct_0(B_901) | ~l1_pre_topc(A_898) | ~v2_pre_topc(A_898) | v2_struct_0(A_898))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.82/2.31  tff(c_2508, plain, (![H_895, F_897]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', H_895) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), H_895) | ~m1_connsp_2(F_897, '#skF_5', H_895) | ~r1_tarski(F_897, u1_struct_0('#skF_4')) | ~m1_subset_1(H_895, u1_struct_0('#skF_4')) | ~m1_subset_1(H_895, u1_struct_0('#skF_5')) | ~m1_subset_1(F_897, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2291, c_2502])).
% 6.82/2.31  tff(c_2518, plain, (![H_895, F_897]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', H_895) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), H_895) | ~m1_connsp_2(F_897, '#skF_5', H_895) | ~r1_tarski(F_897, u1_struct_0('#skF_4')) | ~m1_subset_1(H_895, u1_struct_0('#skF_4')) | ~m1_subset_1(H_895, u1_struct_0('#skF_5')) | ~m1_subset_1(F_897, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_80, c_78, c_68, c_64, c_62, c_60, c_58, c_56, c_2508])).
% 6.82/2.31  tff(c_3504, plain, (![H_966, F_967]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', H_966) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), H_966) | ~m1_connsp_2(F_967, '#skF_5', H_966) | ~r1_tarski(F_967, u1_struct_0('#skF_4')) | ~m1_subset_1(H_966, u1_struct_0('#skF_4')) | ~m1_subset_1(H_966, u1_struct_0('#skF_5')) | ~m1_subset_1(F_967, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_82, c_70, c_66, c_2518])).
% 6.82/2.31  tff(c_3509, plain, (![F_967]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_967, '#skF_5', '#skF_8') | ~r1_tarski(F_967, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_967, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_2302, c_3504])).
% 6.82/2.31  tff(c_3516, plain, (![F_967]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_connsp_2(F_967, '#skF_5', '#skF_8') | ~r1_tarski(F_967, u1_struct_0('#skF_4')) | ~m1_subset_1(F_967, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_93, c_3509])).
% 6.82/2.31  tff(c_3518, plain, (![F_968]: (~m1_connsp_2(F_968, '#skF_5', '#skF_8') | ~r1_tarski(F_968, u1_struct_0('#skF_4')) | ~m1_subset_1(F_968, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_178, c_3516])).
% 6.82/2.31  tff(c_3524, plain, (![A_969]: (~m1_connsp_2(A_969, '#skF_5', '#skF_8') | ~r1_tarski(A_969, u1_struct_0('#skF_4')) | ~r1_tarski(A_969, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_3518])).
% 6.82/2.31  tff(c_3530, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2613, c_3524])).
% 6.82/2.31  tff(c_3545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3021, c_3530])).
% 6.82/2.31  tff(c_3547, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_92])).
% 6.82/2.31  tff(c_4422, plain, (![B_1050, F_1046, D_1047, A_1049, C_1048]: (r1_tmap_1(D_1047, A_1049, k2_tmap_1(B_1050, A_1049, C_1048, D_1047), F_1046) | ~r1_tmap_1(B_1050, A_1049, C_1048, F_1046) | ~m1_subset_1(F_1046, u1_struct_0(D_1047)) | ~m1_subset_1(F_1046, u1_struct_0(B_1050)) | ~m1_pre_topc(D_1047, B_1050) | v2_struct_0(D_1047) | ~m1_subset_1(C_1048, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_1050), u1_struct_0(A_1049)))) | ~v1_funct_2(C_1048, u1_struct_0(B_1050), u1_struct_0(A_1049)) | ~v1_funct_1(C_1048) | ~l1_pre_topc(B_1050) | ~v2_pre_topc(B_1050) | v2_struct_0(B_1050) | ~l1_pre_topc(A_1049) | ~v2_pre_topc(A_1049) | v2_struct_0(A_1049))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.82/2.31  tff(c_4424, plain, (![D_1047, F_1046]: (r1_tmap_1(D_1047, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1047), F_1046) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1046) | ~m1_subset_1(F_1046, u1_struct_0(D_1047)) | ~m1_subset_1(F_1046, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1047, '#skF_5') | v2_struct_0(D_1047) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_4422])).
% 6.82/2.31  tff(c_4430, plain, (![D_1047, F_1046]: (r1_tmap_1(D_1047, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1047), F_1046) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1046) | ~m1_subset_1(F_1046, u1_struct_0(D_1047)) | ~m1_subset_1(F_1046, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1047, '#skF_5') | v2_struct_0(D_1047) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_177, c_116, c_62, c_60, c_4424])).
% 6.82/2.31  tff(c_4431, plain, (![D_1047, F_1046]: (r1_tmap_1(D_1047, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1047), F_1046) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_1046) | ~m1_subset_1(F_1046, u1_struct_0(D_1047)) | ~m1_subset_1(F_1046, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_1047, '#skF_5') | v2_struct_0(D_1047))), inference(negUnitSimplification, [status(thm)], [c_82, c_66, c_4430])).
% 6.82/2.31  tff(c_4255, plain, (![E_1035, B_1033, A_1031, D_1032, C_1034]: (k3_tmap_1(A_1031, B_1033, C_1034, D_1032, E_1035)=k2_partfun1(u1_struct_0(C_1034), u1_struct_0(B_1033), E_1035, u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, C_1034) | ~m1_subset_1(E_1035, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1034), u1_struct_0(B_1033)))) | ~v1_funct_2(E_1035, u1_struct_0(C_1034), u1_struct_0(B_1033)) | ~v1_funct_1(E_1035) | ~m1_pre_topc(D_1032, A_1031) | ~m1_pre_topc(C_1034, A_1031) | ~l1_pre_topc(B_1033) | ~v2_pre_topc(B_1033) | v2_struct_0(B_1033) | ~l1_pre_topc(A_1031) | ~v2_pre_topc(A_1031) | v2_struct_0(A_1031))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.82/2.31  tff(c_4257, plain, (![A_1031, D_1032]: (k3_tmap_1(A_1031, '#skF_2', '#skF_5', D_1032, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_1032, A_1031) | ~m1_pre_topc('#skF_5', A_1031) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1031) | ~v2_pre_topc(A_1031) | v2_struct_0(A_1031))), inference(resolution, [status(thm)], [c_58, c_4255])).
% 6.82/2.31  tff(c_4263, plain, (![A_1031, D_1032]: (k3_tmap_1(A_1031, '#skF_2', '#skF_5', D_1032, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1032)) | ~m1_pre_topc(D_1032, '#skF_5') | ~m1_pre_topc(D_1032, A_1031) | ~m1_pre_topc('#skF_5', A_1031) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1031) | ~v2_pre_topc(A_1031) | v2_struct_0(A_1031))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_62, c_60, c_4257])).
% 6.82/2.31  tff(c_4679, plain, (![A_1086, D_1087]: (k3_tmap_1(A_1086, '#skF_2', '#skF_5', D_1087, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1087)) | ~m1_pre_topc(D_1087, '#skF_5') | ~m1_pre_topc(D_1087, A_1086) | ~m1_pre_topc('#skF_5', A_1086) | ~l1_pre_topc(A_1086) | ~v2_pre_topc(A_1086) | v2_struct_0(A_1086))), inference(negUnitSimplification, [status(thm)], [c_82, c_4263])).
% 6.82/2.31  tff(c_4687, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4679])).
% 6.82/2.31  tff(c_4705, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_64, c_56, c_4687])).
% 6.82/2.31  tff(c_4706, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_4705])).
% 6.82/2.31  tff(c_4174, plain, (![A_1023, B_1024, C_1025, D_1026]: (k2_partfun1(u1_struct_0(A_1023), u1_struct_0(B_1024), C_1025, u1_struct_0(D_1026))=k2_tmap_1(A_1023, B_1024, C_1025, D_1026) | ~m1_pre_topc(D_1026, A_1023) | ~m1_subset_1(C_1025, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1023), u1_struct_0(B_1024)))) | ~v1_funct_2(C_1025, u1_struct_0(A_1023), u1_struct_0(B_1024)) | ~v1_funct_1(C_1025) | ~l1_pre_topc(B_1024) | ~v2_pre_topc(B_1024) | v2_struct_0(B_1024) | ~l1_pre_topc(A_1023) | ~v2_pre_topc(A_1023) | v2_struct_0(A_1023))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.82/2.31  tff(c_4176, plain, (![D_1026]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1026))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1026) | ~m1_pre_topc(D_1026, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4174])).
% 6.82/2.31  tff(c_4182, plain, (![D_1026]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1026))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1026) | ~m1_pre_topc(D_1026, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_116, c_80, c_78, c_62, c_60, c_4176])).
% 6.82/2.31  tff(c_4183, plain, (![D_1026]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_1026))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_1026) | ~m1_pre_topc(D_1026, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_4182])).
% 6.82/2.31  tff(c_4806, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4706, c_4183])).
% 6.82/2.31  tff(c_4813, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4806])).
% 6.82/2.31  tff(c_3546, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_92])).
% 6.82/2.31  tff(c_4818, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4813, c_3546])).
% 6.82/2.31  tff(c_4844, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_4431, c_4818])).
% 6.82/2.31  tff(c_4847, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_93, c_3547, c_4844])).
% 6.82/2.31  tff(c_4849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_4847])).
% 6.82/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.31  
% 6.82/2.31  Inference rules
% 6.82/2.31  ----------------------
% 6.82/2.31  #Ref     : 0
% 6.82/2.31  #Sup     : 997
% 6.82/2.31  #Fact    : 0
% 6.82/2.31  #Define  : 0
% 6.82/2.31  #Split   : 32
% 6.82/2.31  #Chain   : 0
% 6.82/2.31  #Close   : 0
% 6.82/2.31  
% 6.82/2.31  Ordering : KBO
% 6.82/2.31  
% 6.82/2.31  Simplification rules
% 6.82/2.31  ----------------------
% 6.82/2.31  #Subsume      : 394
% 6.82/2.31  #Demod        : 802
% 6.82/2.31  #Tautology    : 240
% 6.82/2.31  #SimpNegUnit  : 79
% 6.82/2.31  #BackRed      : 13
% 6.82/2.31  
% 6.82/2.31  #Partial instantiations: 0
% 6.82/2.31  #Strategies tried      : 1
% 6.82/2.31  
% 6.82/2.31  Timing (in seconds)
% 6.82/2.31  ----------------------
% 6.82/2.31  Preprocessing        : 0.43
% 6.82/2.31  Parsing              : 0.22
% 6.82/2.31  CNF conversion       : 0.07
% 6.82/2.31  Main loop            : 1.09
% 6.82/2.31  Inferencing          : 0.35
% 6.82/2.31  Reduction            : 0.37
% 6.82/2.31  Demodulation         : 0.26
% 6.82/2.31  BG Simplification    : 0.04
% 6.82/2.31  Subsumption          : 0.26
% 6.82/2.31  Abstraction          : 0.04
% 6.82/2.31  MUC search           : 0.00
% 6.82/2.31  Cooper               : 0.00
% 6.82/2.31  Total                : 1.57
% 6.82/2.31  Index Insertion      : 0.00
% 6.82/2.31  Index Deletion       : 0.00
% 6.82/2.31  Index Matching       : 0.00
% 6.82/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
