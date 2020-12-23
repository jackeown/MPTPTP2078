%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:25 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 396 expanded)
%              Number of leaves         :   40 ( 164 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 (2950 expanded)
%              Number of equality atoms :    5 ( 105 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_283,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( m1_connsp_2(D,A,C)
                            & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_225,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_170,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_38,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_46,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_89,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_40,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_95,plain,(
    ! [B_700,A_701] :
      ( l1_pre_topc(B_700)
      | ~ m1_pre_topc(B_700,A_701)
      | ~ l1_pre_topc(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_95])).

tff(c_108,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_101])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_311,plain,(
    ! [C_731,A_732,B_733] :
      ( m1_subset_1(C_731,k1_zfmisc_1(u1_struct_0(A_732)))
      | ~ m1_subset_1(C_731,k1_zfmisc_1(u1_struct_0(B_733)))
      | ~ m1_pre_topc(B_733,A_732)
      | ~ l1_pre_topc(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_406,plain,(
    ! [A_745,A_746,B_747] :
      ( m1_subset_1(A_745,k1_zfmisc_1(u1_struct_0(A_746)))
      | ~ m1_pre_topc(B_747,A_746)
      | ~ l1_pre_topc(A_746)
      | ~ r1_tarski(A_745,u1_struct_0(B_747)) ) ),
    inference(resolution,[status(thm)],[c_6,c_311])).

tff(c_414,plain,(
    ! [A_745] :
      ( m1_subset_1(A_745,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ r1_tarski(A_745,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_406])).

tff(c_431,plain,(
    ! [A_748] :
      ( m1_subset_1(A_748,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski(A_748,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_414])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_448,plain,(
    ! [A_749] :
      ( r1_tarski(A_749,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_749,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_431,c_4])).

tff(c_470,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_448])).

tff(c_146,plain,(
    ! [B_709,A_710] :
      ( v2_pre_topc(B_709)
      | ~ m1_pre_topc(B_709,A_710)
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_152,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_146])).

tff(c_161,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_152])).

tff(c_20,plain,(
    ! [A_37,B_51] :
      ( r2_hidden('#skF_2'(A_37,B_51),B_51)
      | v3_pre_topc(B_51,A_37)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_433,plain,(
    ! [A_748] :
      ( r2_hidden('#skF_2'('#skF_6',A_748),A_748)
      | v3_pre_topc(A_748,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_748,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_431,c_20])).

tff(c_443,plain,(
    ! [A_748] :
      ( r2_hidden('#skF_2'('#skF_6',A_748),A_748)
      | v3_pre_topc(A_748,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_748,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_108,c_433])).

tff(c_680,plain,(
    ! [A_769] :
      ( r2_hidden('#skF_2'('#skF_6',A_769),A_769)
      | v3_pre_topc(A_769,'#skF_6')
      | ~ r1_tarski(A_769,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_443])).

tff(c_165,plain,(
    ! [A_711,C_712,B_713] :
      ( m1_subset_1(A_711,C_712)
      | ~ m1_subset_1(B_713,k1_zfmisc_1(C_712))
      | ~ r2_hidden(A_711,B_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_711,B_5,A_4] :
      ( m1_subset_1(A_711,B_5)
      | ~ r2_hidden(A_711,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_1352,plain,(
    ! [A_820,B_821] :
      ( m1_subset_1('#skF_2'('#skF_6',A_820),B_821)
      | ~ r1_tarski(A_820,B_821)
      | v3_pre_topc(A_820,'#skF_6')
      | ~ r1_tarski(A_820,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_680,c_173])).

tff(c_1394,plain,(
    ! [B_821] :
      ( m1_subset_1('#skF_2'('#skF_6','#skF_8'),B_821)
      | ~ r1_tarski('#skF_8',B_821)
      | v3_pre_topc('#skF_8','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_1352])).

tff(c_1395,plain,(
    v3_pre_topc('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_42,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_709,plain,(
    ! [A_773,B_774,C_775] :
      ( r1_tarski('#skF_1'(A_773,B_774,C_775),B_774)
      | ~ r2_hidden(C_775,B_774)
      | ~ m1_subset_1(C_775,u1_struct_0(A_773))
      | ~ v3_pre_topc(B_774,A_773)
      | ~ m1_subset_1(B_774,k1_zfmisc_1(u1_struct_0(A_773)))
      | ~ l1_pre_topc(A_773)
      | ~ v2_pre_topc(A_773)
      | v2_struct_0(A_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_736,plain,(
    ! [A_773,A_4,C_775] :
      ( r1_tarski('#skF_1'(A_773,A_4,C_775),A_4)
      | ~ r2_hidden(C_775,A_4)
      | ~ m1_subset_1(C_775,u1_struct_0(A_773))
      | ~ v3_pre_topc(A_4,A_773)
      | ~ l1_pre_topc(A_773)
      | ~ v2_pre_topc(A_773)
      | v2_struct_0(A_773)
      | ~ r1_tarski(A_4,u1_struct_0(A_773)) ) ),
    inference(resolution,[status(thm)],[c_6,c_709])).

tff(c_854,plain,(
    ! [A_788,B_789,C_790] :
      ( m1_connsp_2('#skF_1'(A_788,B_789,C_790),A_788,C_790)
      | ~ r2_hidden(C_790,B_789)
      | ~ m1_subset_1(C_790,u1_struct_0(A_788))
      | ~ v3_pre_topc(B_789,A_788)
      | ~ m1_subset_1(B_789,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2242,plain,(
    ! [A_876,A_877,C_878] :
      ( m1_connsp_2('#skF_1'(A_876,A_877,C_878),A_876,C_878)
      | ~ r2_hidden(C_878,A_877)
      | ~ m1_subset_1(C_878,u1_struct_0(A_876))
      | ~ v3_pre_topc(A_877,A_876)
      | ~ l1_pre_topc(A_876)
      | ~ v2_pre_topc(A_876)
      | v2_struct_0(A_876)
      | ~ r1_tarski(A_877,u1_struct_0(A_876)) ) ),
    inference(resolution,[status(thm)],[c_6,c_854])).

tff(c_128,plain,(
    ! [A_704,C_705,B_706] :
      ( r1_tarski(A_704,C_705)
      | ~ r1_tarski(B_706,C_705)
      | ~ r1_tarski(A_704,B_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_704] :
      ( r1_tarski(A_704,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_704,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_128])).

tff(c_424,plain,(
    ! [A_745] :
      ( m1_subset_1(A_745,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r1_tarski(A_745,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_414])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_87,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_86])).

tff(c_127,plain,(
    r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_10')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_88,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_258,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_88])).

tff(c_76,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_56,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_1700,plain,(
    ! [A_845,B_847,E_848,F_850,C_846,H_849,D_844] :
      ( r1_tmap_1(D_844,B_847,E_848,H_849)
      | ~ r1_tmap_1(C_846,B_847,k3_tmap_1(A_845,B_847,D_844,C_846,E_848),H_849)
      | ~ m1_connsp_2(F_850,D_844,H_849)
      | ~ r1_tarski(F_850,u1_struct_0(C_846))
      | ~ m1_subset_1(H_849,u1_struct_0(C_846))
      | ~ m1_subset_1(H_849,u1_struct_0(D_844))
      | ~ m1_subset_1(F_850,k1_zfmisc_1(u1_struct_0(D_844)))
      | ~ m1_pre_topc(C_846,D_844)
      | ~ m1_subset_1(E_848,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_844),u1_struct_0(B_847))))
      | ~ v1_funct_2(E_848,u1_struct_0(D_844),u1_struct_0(B_847))
      | ~ v1_funct_1(E_848)
      | ~ m1_pre_topc(D_844,A_845)
      | v2_struct_0(D_844)
      | ~ m1_pre_topc(C_846,A_845)
      | v2_struct_0(C_846)
      | ~ l1_pre_topc(B_847)
      | ~ v2_pre_topc(B_847)
      | v2_struct_0(B_847)
      | ~ l1_pre_topc(A_845)
      | ~ v2_pre_topc(A_845)
      | v2_struct_0(A_845) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1702,plain,(
    ! [F_850] :
      ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9')
      | ~ m1_connsp_2(F_850,'#skF_6','#skF_9')
      | ~ r1_tarski(F_850,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_850,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_4')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_1700])).

tff(c_1705,plain,(
    ! [F_850] :
      ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9')
      | ~ m1_connsp_2(F_850,'#skF_6','#skF_9')
      | ~ r1_tarski(F_850,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_850,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_76,c_74,c_64,c_60,c_58,c_56,c_54,c_52,c_48,c_89,c_1702])).

tff(c_1707,plain,(
    ! [F_851] :
      ( ~ m1_connsp_2(F_851,'#skF_6','#skF_9')
      | ~ r1_tarski(F_851,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_851,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_78,c_66,c_62,c_258,c_1705])).

tff(c_1772,plain,(
    ! [A_854] :
      ( ~ m1_connsp_2(A_854,'#skF_6','#skF_9')
      | ~ r1_tarski(A_854,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_424,c_1707])).

tff(c_1832,plain,(
    ! [A_704] :
      ( ~ m1_connsp_2(A_704,'#skF_6','#skF_9')
      | ~ r1_tarski(A_704,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_137,c_1772])).

tff(c_2246,plain,(
    ! [A_877] :
      ( ~ r1_tarski('#skF_1'('#skF_6',A_877,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_9',A_877)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(A_877,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_877,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2242,c_1832])).

tff(c_2252,plain,(
    ! [A_877] :
      ( ~ r1_tarski('#skF_1'('#skF_6',A_877,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_9',A_877)
      | ~ v3_pre_topc(A_877,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_877,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_108,c_48,c_2246])).

tff(c_2391,plain,(
    ! [A_882] :
      ( ~ r1_tarski('#skF_1'('#skF_6',A_882,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_9',A_882)
      | ~ v3_pre_topc(A_882,'#skF_6')
      | ~ r1_tarski(A_882,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2252])).

tff(c_2395,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc('#skF_8','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ r1_tarski('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_736,c_2391])).

tff(c_2402,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_161,c_108,c_1395,c_48,c_42,c_2395])).

tff(c_2404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2402])).

tff(c_2406,plain,(
    ~ v3_pre_topc('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_44,plain,(
    v3_pre_topc('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_632,plain,(
    ! [D_760,C_761,A_762] :
      ( v3_pre_topc(D_760,C_761)
      | ~ m1_subset_1(D_760,k1_zfmisc_1(u1_struct_0(C_761)))
      | ~ v3_pre_topc(D_760,A_762)
      | ~ m1_pre_topc(C_761,A_762)
      | ~ m1_subset_1(D_760,k1_zfmisc_1(u1_struct_0(A_762)))
      | ~ l1_pre_topc(A_762) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2802,plain,(
    ! [A_919,C_920,A_921] :
      ( v3_pre_topc(A_919,C_920)
      | ~ v3_pre_topc(A_919,A_921)
      | ~ m1_pre_topc(C_920,A_921)
      | ~ m1_subset_1(A_919,k1_zfmisc_1(u1_struct_0(A_921)))
      | ~ l1_pre_topc(A_921)
      | ~ r1_tarski(A_919,u1_struct_0(C_920)) ) ),
    inference(resolution,[status(thm)],[c_6,c_632])).

tff(c_2812,plain,(
    ! [A_919] :
      ( v3_pre_topc(A_919,'#skF_6')
      | ~ v3_pre_topc(A_919,'#skF_4')
      | ~ m1_subset_1(A_919,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_919,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_60,c_2802])).

tff(c_3168,plain,(
    ! [A_934] :
      ( v3_pre_topc(A_934,'#skF_6')
      | ~ v3_pre_topc(A_934,'#skF_4')
      | ~ m1_subset_1(A_934,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_934,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2812])).

tff(c_3213,plain,
    ( v3_pre_topc('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_8','#skF_4')
    | ~ r1_tarski('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_3168])).

tff(c_3239,plain,(
    v3_pre_topc('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_44,c_3213])).

tff(c_3241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2406,c_3239])).

tff(c_3242,plain,(
    r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4600,plain,(
    ! [A_1060,B_1062,D_1064,C_1061,G_1065,E_1063] :
      ( r1_tmap_1(D_1064,B_1062,k3_tmap_1(A_1060,B_1062,C_1061,D_1064,E_1063),G_1065)
      | ~ r1_tmap_1(C_1061,B_1062,E_1063,G_1065)
      | ~ m1_pre_topc(D_1064,C_1061)
      | ~ m1_subset_1(G_1065,u1_struct_0(D_1064))
      | ~ m1_subset_1(G_1065,u1_struct_0(C_1061))
      | ~ m1_subset_1(E_1063,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1061),u1_struct_0(B_1062))))
      | ~ v1_funct_2(E_1063,u1_struct_0(C_1061),u1_struct_0(B_1062))
      | ~ v1_funct_1(E_1063)
      | ~ m1_pre_topc(D_1064,A_1060)
      | v2_struct_0(D_1064)
      | ~ m1_pre_topc(C_1061,A_1060)
      | v2_struct_0(C_1061)
      | ~ l1_pre_topc(B_1062)
      | ~ v2_pre_topc(B_1062)
      | v2_struct_0(B_1062)
      | ~ l1_pre_topc(A_1060)
      | ~ v2_pre_topc(A_1060)
      | v2_struct_0(A_1060) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4608,plain,(
    ! [D_1064,A_1060,G_1065] :
      ( r1_tmap_1(D_1064,'#skF_3',k3_tmap_1(A_1060,'#skF_3','#skF_6',D_1064,'#skF_7'),G_1065)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_1065)
      | ~ m1_pre_topc(D_1064,'#skF_6')
      | ~ m1_subset_1(G_1065,u1_struct_0(D_1064))
      | ~ m1_subset_1(G_1065,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_1064,A_1060)
      | v2_struct_0(D_1064)
      | ~ m1_pre_topc('#skF_6',A_1060)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_1060)
      | ~ v2_pre_topc(A_1060)
      | v2_struct_0(A_1060) ) ),
    inference(resolution,[status(thm)],[c_54,c_4600])).

tff(c_4616,plain,(
    ! [D_1064,A_1060,G_1065] :
      ( r1_tmap_1(D_1064,'#skF_3',k3_tmap_1(A_1060,'#skF_3','#skF_6',D_1064,'#skF_7'),G_1065)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_1065)
      | ~ m1_pre_topc(D_1064,'#skF_6')
      | ~ m1_subset_1(G_1065,u1_struct_0(D_1064))
      | ~ m1_subset_1(G_1065,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_1064,A_1060)
      | v2_struct_0(D_1064)
      | ~ m1_pre_topc('#skF_6',A_1060)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_1060)
      | ~ v2_pre_topc(A_1060)
      | v2_struct_0(A_1060) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_4608])).

tff(c_5323,plain,(
    ! [D_1118,A_1119,G_1120] :
      ( r1_tmap_1(D_1118,'#skF_3',k3_tmap_1(A_1119,'#skF_3','#skF_6',D_1118,'#skF_7'),G_1120)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_1120)
      | ~ m1_pre_topc(D_1118,'#skF_6')
      | ~ m1_subset_1(G_1120,u1_struct_0(D_1118))
      | ~ m1_subset_1(G_1120,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_1118,A_1119)
      | v2_struct_0(D_1118)
      | ~ m1_pre_topc('#skF_6',A_1119)
      | ~ l1_pre_topc(A_1119)
      | ~ v2_pre_topc(A_1119)
      | v2_struct_0(A_1119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_4616])).

tff(c_3243,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_5328,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_9')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5323,c_3243])).

tff(c_5335,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_64,c_48,c_89,c_52,c_3242,c_5328])).

tff(c_5337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_5335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:26:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.19/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.48  
% 7.19/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.48  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 7.19/2.48  
% 7.19/2.48  %Foreground sorts:
% 7.19/2.48  
% 7.19/2.48  
% 7.19/2.48  %Background operators:
% 7.19/2.48  
% 7.19/2.48  
% 7.19/2.48  %Foreground operators:
% 7.19/2.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.19/2.48  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.19/2.48  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.19/2.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.19/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.19/2.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.19/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.19/2.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.19/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.19/2.48  tff('#skF_7', type, '#skF_7': $i).
% 7.19/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.19/2.48  tff('#skF_10', type, '#skF_10': $i).
% 7.19/2.48  tff('#skF_5', type, '#skF_5': $i).
% 7.19/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.19/2.48  tff('#skF_6', type, '#skF_6': $i).
% 7.19/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.19/2.48  tff('#skF_9', type, '#skF_9': $i).
% 7.19/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.19/2.48  tff('#skF_8', type, '#skF_8': $i).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.19/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.19/2.48  tff('#skF_4', type, '#skF_4': $i).
% 7.19/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.19/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.19/2.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.19/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.19/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.19/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.19/2.48  
% 7.19/2.51  tff(f_283, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 7.19/2.51  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.19/2.51  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.19/2.51  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.19/2.51  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.19/2.51  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 7.19/2.51  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.19/2.51  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.19/2.51  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 7.19/2.51  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 7.19/2.51  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 7.19/2.51  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_48, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_38, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_46, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_89, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 7.19/2.51  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_40, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_95, plain, (![B_700, A_701]: (l1_pre_topc(B_700) | ~m1_pre_topc(B_700, A_701) | ~l1_pre_topc(A_701))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.19/2.51  tff(c_101, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_95])).
% 7.19/2.51  tff(c_108, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_101])).
% 7.19/2.51  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.19/2.51  tff(c_311, plain, (![C_731, A_732, B_733]: (m1_subset_1(C_731, k1_zfmisc_1(u1_struct_0(A_732))) | ~m1_subset_1(C_731, k1_zfmisc_1(u1_struct_0(B_733))) | ~m1_pre_topc(B_733, A_732) | ~l1_pre_topc(A_732))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.19/2.51  tff(c_406, plain, (![A_745, A_746, B_747]: (m1_subset_1(A_745, k1_zfmisc_1(u1_struct_0(A_746))) | ~m1_pre_topc(B_747, A_746) | ~l1_pre_topc(A_746) | ~r1_tarski(A_745, u1_struct_0(B_747)))), inference(resolution, [status(thm)], [c_6, c_311])).
% 7.19/2.51  tff(c_414, plain, (![A_745]: (m1_subset_1(A_745, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~r1_tarski(A_745, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_52, c_406])).
% 7.19/2.51  tff(c_431, plain, (![A_748]: (m1_subset_1(A_748, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski(A_748, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_414])).
% 7.19/2.51  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.19/2.51  tff(c_448, plain, (![A_749]: (r1_tarski(A_749, u1_struct_0('#skF_6')) | ~r1_tarski(A_749, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_431, c_4])).
% 7.19/2.51  tff(c_470, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_448])).
% 7.19/2.51  tff(c_146, plain, (![B_709, A_710]: (v2_pre_topc(B_709) | ~m1_pre_topc(B_709, A_710) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.19/2.51  tff(c_152, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_146])).
% 7.19/2.51  tff(c_161, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_152])).
% 7.19/2.51  tff(c_20, plain, (![A_37, B_51]: (r2_hidden('#skF_2'(A_37, B_51), B_51) | v3_pre_topc(B_51, A_37) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.19/2.51  tff(c_433, plain, (![A_748]: (r2_hidden('#skF_2'('#skF_6', A_748), A_748) | v3_pre_topc(A_748, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_748, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_431, c_20])).
% 7.19/2.51  tff(c_443, plain, (![A_748]: (r2_hidden('#skF_2'('#skF_6', A_748), A_748) | v3_pre_topc(A_748, '#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_748, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_108, c_433])).
% 7.19/2.51  tff(c_680, plain, (![A_769]: (r2_hidden('#skF_2'('#skF_6', A_769), A_769) | v3_pre_topc(A_769, '#skF_6') | ~r1_tarski(A_769, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_443])).
% 7.19/2.51  tff(c_165, plain, (![A_711, C_712, B_713]: (m1_subset_1(A_711, C_712) | ~m1_subset_1(B_713, k1_zfmisc_1(C_712)) | ~r2_hidden(A_711, B_713))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.19/2.51  tff(c_173, plain, (![A_711, B_5, A_4]: (m1_subset_1(A_711, B_5) | ~r2_hidden(A_711, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_165])).
% 7.19/2.51  tff(c_1352, plain, (![A_820, B_821]: (m1_subset_1('#skF_2'('#skF_6', A_820), B_821) | ~r1_tarski(A_820, B_821) | v3_pre_topc(A_820, '#skF_6') | ~r1_tarski(A_820, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_680, c_173])).
% 7.19/2.51  tff(c_1394, plain, (![B_821]: (m1_subset_1('#skF_2'('#skF_6', '#skF_8'), B_821) | ~r1_tarski('#skF_8', B_821) | v3_pre_topc('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1352])).
% 7.19/2.51  tff(c_1395, plain, (v3_pre_topc('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_1394])).
% 7.19/2.51  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_709, plain, (![A_773, B_774, C_775]: (r1_tarski('#skF_1'(A_773, B_774, C_775), B_774) | ~r2_hidden(C_775, B_774) | ~m1_subset_1(C_775, u1_struct_0(A_773)) | ~v3_pre_topc(B_774, A_773) | ~m1_subset_1(B_774, k1_zfmisc_1(u1_struct_0(A_773))) | ~l1_pre_topc(A_773) | ~v2_pre_topc(A_773) | v2_struct_0(A_773))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.19/2.51  tff(c_736, plain, (![A_773, A_4, C_775]: (r1_tarski('#skF_1'(A_773, A_4, C_775), A_4) | ~r2_hidden(C_775, A_4) | ~m1_subset_1(C_775, u1_struct_0(A_773)) | ~v3_pre_topc(A_4, A_773) | ~l1_pre_topc(A_773) | ~v2_pre_topc(A_773) | v2_struct_0(A_773) | ~r1_tarski(A_4, u1_struct_0(A_773)))), inference(resolution, [status(thm)], [c_6, c_709])).
% 7.19/2.51  tff(c_854, plain, (![A_788, B_789, C_790]: (m1_connsp_2('#skF_1'(A_788, B_789, C_790), A_788, C_790) | ~r2_hidden(C_790, B_789) | ~m1_subset_1(C_790, u1_struct_0(A_788)) | ~v3_pre_topc(B_789, A_788) | ~m1_subset_1(B_789, k1_zfmisc_1(u1_struct_0(A_788))) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.19/2.51  tff(c_2242, plain, (![A_876, A_877, C_878]: (m1_connsp_2('#skF_1'(A_876, A_877, C_878), A_876, C_878) | ~r2_hidden(C_878, A_877) | ~m1_subset_1(C_878, u1_struct_0(A_876)) | ~v3_pre_topc(A_877, A_876) | ~l1_pre_topc(A_876) | ~v2_pre_topc(A_876) | v2_struct_0(A_876) | ~r1_tarski(A_877, u1_struct_0(A_876)))), inference(resolution, [status(thm)], [c_6, c_854])).
% 7.19/2.51  tff(c_128, plain, (![A_704, C_705, B_706]: (r1_tarski(A_704, C_705) | ~r1_tarski(B_706, C_705) | ~r1_tarski(A_704, B_706))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.19/2.51  tff(c_137, plain, (![A_704]: (r1_tarski(A_704, u1_struct_0('#skF_5')) | ~r1_tarski(A_704, '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_128])).
% 7.19/2.51  tff(c_424, plain, (![A_745]: (m1_subset_1(A_745, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r1_tarski(A_745, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_414])).
% 7.19/2.51  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_86, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_87, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_86])).
% 7.19/2.51  tff(c_127, plain, (r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_87])).
% 7.19/2.51  tff(c_80, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_10') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_88, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 7.19/2.51  tff(c_258, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_88])).
% 7.19/2.51  tff(c_76, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_56, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_1700, plain, (![A_845, B_847, E_848, F_850, C_846, H_849, D_844]: (r1_tmap_1(D_844, B_847, E_848, H_849) | ~r1_tmap_1(C_846, B_847, k3_tmap_1(A_845, B_847, D_844, C_846, E_848), H_849) | ~m1_connsp_2(F_850, D_844, H_849) | ~r1_tarski(F_850, u1_struct_0(C_846)) | ~m1_subset_1(H_849, u1_struct_0(C_846)) | ~m1_subset_1(H_849, u1_struct_0(D_844)) | ~m1_subset_1(F_850, k1_zfmisc_1(u1_struct_0(D_844))) | ~m1_pre_topc(C_846, D_844) | ~m1_subset_1(E_848, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_844), u1_struct_0(B_847)))) | ~v1_funct_2(E_848, u1_struct_0(D_844), u1_struct_0(B_847)) | ~v1_funct_1(E_848) | ~m1_pre_topc(D_844, A_845) | v2_struct_0(D_844) | ~m1_pre_topc(C_846, A_845) | v2_struct_0(C_846) | ~l1_pre_topc(B_847) | ~v2_pre_topc(B_847) | v2_struct_0(B_847) | ~l1_pre_topc(A_845) | ~v2_pre_topc(A_845) | v2_struct_0(A_845))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.19/2.51  tff(c_1702, plain, (![F_850]: (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9') | ~m1_connsp_2(F_850, '#skF_6', '#skF_9') | ~r1_tarski(F_850, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1(F_850, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_127, c_1700])).
% 7.19/2.51  tff(c_1705, plain, (![F_850]: (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9') | ~m1_connsp_2(F_850, '#skF_6', '#skF_9') | ~r1_tarski(F_850, u1_struct_0('#skF_5')) | ~m1_subset_1(F_850, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_76, c_74, c_64, c_60, c_58, c_56, c_54, c_52, c_48, c_89, c_1702])).
% 7.19/2.51  tff(c_1707, plain, (![F_851]: (~m1_connsp_2(F_851, '#skF_6', '#skF_9') | ~r1_tarski(F_851, u1_struct_0('#skF_5')) | ~m1_subset_1(F_851, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_78, c_66, c_62, c_258, c_1705])).
% 7.19/2.51  tff(c_1772, plain, (![A_854]: (~m1_connsp_2(A_854, '#skF_6', '#skF_9') | ~r1_tarski(A_854, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_424, c_1707])).
% 7.19/2.51  tff(c_1832, plain, (![A_704]: (~m1_connsp_2(A_704, '#skF_6', '#skF_9') | ~r1_tarski(A_704, '#skF_8'))), inference(resolution, [status(thm)], [c_137, c_1772])).
% 7.19/2.51  tff(c_2246, plain, (![A_877]: (~r1_tarski('#skF_1'('#skF_6', A_877, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', A_877) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v3_pre_topc(A_877, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_877, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_2242, c_1832])).
% 7.19/2.51  tff(c_2252, plain, (![A_877]: (~r1_tarski('#skF_1'('#skF_6', A_877, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', A_877) | ~v3_pre_topc(A_877, '#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_877, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_108, c_48, c_2246])).
% 7.19/2.51  tff(c_2391, plain, (![A_882]: (~r1_tarski('#skF_1'('#skF_6', A_882, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_9', A_882) | ~v3_pre_topc(A_882, '#skF_6') | ~r1_tarski(A_882, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_62, c_2252])).
% 7.19/2.51  tff(c_2395, plain, (~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~v3_pre_topc('#skF_8', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_736, c_2391])).
% 7.19/2.51  tff(c_2402, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_161, c_108, c_1395, c_48, c_42, c_2395])).
% 7.19/2.51  tff(c_2404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2402])).
% 7.19/2.51  tff(c_2406, plain, (~v3_pre_topc('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_1394])).
% 7.19/2.51  tff(c_44, plain, (v3_pre_topc('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_283])).
% 7.19/2.51  tff(c_632, plain, (![D_760, C_761, A_762]: (v3_pre_topc(D_760, C_761) | ~m1_subset_1(D_760, k1_zfmisc_1(u1_struct_0(C_761))) | ~v3_pre_topc(D_760, A_762) | ~m1_pre_topc(C_761, A_762) | ~m1_subset_1(D_760, k1_zfmisc_1(u1_struct_0(A_762))) | ~l1_pre_topc(A_762))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.19/2.51  tff(c_2802, plain, (![A_919, C_920, A_921]: (v3_pre_topc(A_919, C_920) | ~v3_pre_topc(A_919, A_921) | ~m1_pre_topc(C_920, A_921) | ~m1_subset_1(A_919, k1_zfmisc_1(u1_struct_0(A_921))) | ~l1_pre_topc(A_921) | ~r1_tarski(A_919, u1_struct_0(C_920)))), inference(resolution, [status(thm)], [c_6, c_632])).
% 7.19/2.51  tff(c_2812, plain, (![A_919]: (v3_pre_topc(A_919, '#skF_6') | ~v3_pre_topc(A_919, '#skF_4') | ~m1_subset_1(A_919, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_919, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_60, c_2802])).
% 7.19/2.51  tff(c_3168, plain, (![A_934]: (v3_pre_topc(A_934, '#skF_6') | ~v3_pre_topc(A_934, '#skF_4') | ~m1_subset_1(A_934, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_934, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2812])).
% 7.19/2.51  tff(c_3213, plain, (v3_pre_topc('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_8', '#skF_4') | ~r1_tarski('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_3168])).
% 7.19/2.51  tff(c_3239, plain, (v3_pre_topc('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_44, c_3213])).
% 7.19/2.51  tff(c_3241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2406, c_3239])).
% 7.19/2.51  tff(c_3242, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_87])).
% 7.19/2.51  tff(c_4600, plain, (![A_1060, B_1062, D_1064, C_1061, G_1065, E_1063]: (r1_tmap_1(D_1064, B_1062, k3_tmap_1(A_1060, B_1062, C_1061, D_1064, E_1063), G_1065) | ~r1_tmap_1(C_1061, B_1062, E_1063, G_1065) | ~m1_pre_topc(D_1064, C_1061) | ~m1_subset_1(G_1065, u1_struct_0(D_1064)) | ~m1_subset_1(G_1065, u1_struct_0(C_1061)) | ~m1_subset_1(E_1063, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1061), u1_struct_0(B_1062)))) | ~v1_funct_2(E_1063, u1_struct_0(C_1061), u1_struct_0(B_1062)) | ~v1_funct_1(E_1063) | ~m1_pre_topc(D_1064, A_1060) | v2_struct_0(D_1064) | ~m1_pre_topc(C_1061, A_1060) | v2_struct_0(C_1061) | ~l1_pre_topc(B_1062) | ~v2_pre_topc(B_1062) | v2_struct_0(B_1062) | ~l1_pre_topc(A_1060) | ~v2_pre_topc(A_1060) | v2_struct_0(A_1060))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.19/2.51  tff(c_4608, plain, (![D_1064, A_1060, G_1065]: (r1_tmap_1(D_1064, '#skF_3', k3_tmap_1(A_1060, '#skF_3', '#skF_6', D_1064, '#skF_7'), G_1065) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_1065) | ~m1_pre_topc(D_1064, '#skF_6') | ~m1_subset_1(G_1065, u1_struct_0(D_1064)) | ~m1_subset_1(G_1065, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_1064, A_1060) | v2_struct_0(D_1064) | ~m1_pre_topc('#skF_6', A_1060) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_1060) | ~v2_pre_topc(A_1060) | v2_struct_0(A_1060))), inference(resolution, [status(thm)], [c_54, c_4600])).
% 7.19/2.51  tff(c_4616, plain, (![D_1064, A_1060, G_1065]: (r1_tmap_1(D_1064, '#skF_3', k3_tmap_1(A_1060, '#skF_3', '#skF_6', D_1064, '#skF_7'), G_1065) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_1065) | ~m1_pre_topc(D_1064, '#skF_6') | ~m1_subset_1(G_1065, u1_struct_0(D_1064)) | ~m1_subset_1(G_1065, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_1064, A_1060) | v2_struct_0(D_1064) | ~m1_pre_topc('#skF_6', A_1060) | v2_struct_0('#skF_6') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_1060) | ~v2_pre_topc(A_1060) | v2_struct_0(A_1060))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_4608])).
% 7.19/2.51  tff(c_5323, plain, (![D_1118, A_1119, G_1120]: (r1_tmap_1(D_1118, '#skF_3', k3_tmap_1(A_1119, '#skF_3', '#skF_6', D_1118, '#skF_7'), G_1120) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_1120) | ~m1_pre_topc(D_1118, '#skF_6') | ~m1_subset_1(G_1120, u1_struct_0(D_1118)) | ~m1_subset_1(G_1120, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_1118, A_1119) | v2_struct_0(D_1118) | ~m1_pre_topc('#skF_6', A_1119) | ~l1_pre_topc(A_1119) | ~v2_pre_topc(A_1119) | v2_struct_0(A_1119))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_4616])).
% 7.19/2.51  tff(c_3243, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_87])).
% 7.19/2.51  tff(c_5328, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_9') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5323, c_3243])).
% 7.19/2.51  tff(c_5335, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_64, c_48, c_89, c_52, c_3242, c_5328])).
% 7.19/2.51  tff(c_5337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_5335])).
% 7.19/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/2.51  
% 7.19/2.51  Inference rules
% 7.19/2.51  ----------------------
% 7.19/2.51  #Ref     : 0
% 7.19/2.51  #Sup     : 1155
% 7.19/2.51  #Fact    : 0
% 7.19/2.51  #Define  : 0
% 7.19/2.51  #Split   : 25
% 7.19/2.51  #Chain   : 0
% 7.19/2.51  #Close   : 0
% 7.19/2.51  
% 7.19/2.51  Ordering : KBO
% 7.19/2.51  
% 7.19/2.51  Simplification rules
% 7.19/2.51  ----------------------
% 7.19/2.51  #Subsume      : 295
% 7.19/2.51  #Demod        : 603
% 7.19/2.51  #Tautology    : 127
% 7.19/2.51  #SimpNegUnit  : 58
% 7.19/2.51  #BackRed      : 0
% 7.19/2.51  
% 7.19/2.51  #Partial instantiations: 0
% 7.19/2.51  #Strategies tried      : 1
% 7.19/2.51  
% 7.19/2.51  Timing (in seconds)
% 7.19/2.51  ----------------------
% 7.19/2.52  Preprocessing        : 0.44
% 7.19/2.52  Parsing              : 0.22
% 7.19/2.52  CNF conversion       : 0.07
% 7.19/2.52  Main loop            : 1.30
% 7.19/2.52  Inferencing          : 0.41
% 7.19/2.52  Reduction            : 0.41
% 7.19/2.52  Demodulation         : 0.28
% 7.19/2.52  BG Simplification    : 0.05
% 7.19/2.52  Subsumption          : 0.32
% 7.19/2.52  Abstraction          : 0.05
% 7.19/2.52  MUC search           : 0.00
% 7.19/2.52  Cooper               : 0.00
% 7.19/2.52  Total                : 1.79
% 7.19/2.52  Index Insertion      : 0.00
% 7.19/2.52  Index Deletion       : 0.00
% 7.19/2.52  Index Matching       : 0.00
% 7.19/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
