%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 4.91s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 250 expanded)
%              Number of leaves         :   36 ( 112 expanded)
%              Depth                    :   12
%              Number of atoms          :  377 (1866 expanded)
%              Number of equality atoms :    6 (  71 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_259,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_201,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ( ( v3_pre_topc(C,A)
                          & r1_tarski(C,u1_struct_0(B))
                          & r1_tarski(D,C)
                          & D = E )
                       => ( v3_pre_topc(E,B)
                        <=> v3_pre_topc(D,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

tff(f_173,axiom,(
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

tff(f_116,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_34,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_102,plain,(
    ! [B_688,A_689] :
      ( l1_pre_topc(B_688)
      | ~ m1_pre_topc(B_688,A_689)
      | ~ l1_pre_topc(A_689) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_118,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_111])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_36,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_201,plain,(
    ! [B_704,A_705] :
      ( m1_subset_1(u1_struct_0(B_704),k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ m1_pre_topc(B_704,A_705)
      | ~ l1_pre_topc(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_205,plain,(
    ! [B_704,A_705] :
      ( r1_tarski(u1_struct_0(B_704),u1_struct_0(A_705))
      | ~ m1_pre_topc(B_704,A_705)
      | ~ l1_pre_topc(A_705) ) ),
    inference(resolution,[status(thm)],[c_201,c_14])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [C_696,B_697,A_698] :
      ( r2_hidden(C_696,B_697)
      | ~ r2_hidden(C_696,A_698)
      | ~ r1_tarski(A_698,B_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_233,plain,(
    ! [A_710,B_711,B_712] :
      ( r2_hidden('#skF_1'(A_710,B_711),B_712)
      | ~ r1_tarski(A_710,B_712)
      | r1_tarski(A_710,B_711) ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_301,plain,(
    ! [A_725,B_726,B_727,B_728] :
      ( r2_hidden('#skF_1'(A_725,B_726),B_727)
      | ~ r1_tarski(B_728,B_727)
      | ~ r1_tarski(A_725,B_728)
      | r1_tarski(A_725,B_726) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_1357,plain,(
    ! [A_834,B_835,A_836,B_837] :
      ( r2_hidden('#skF_1'(A_834,B_835),u1_struct_0(A_836))
      | ~ r1_tarski(A_834,u1_struct_0(B_837))
      | r1_tarski(A_834,B_835)
      | ~ m1_pre_topc(B_837,A_836)
      | ~ l1_pre_topc(A_836) ) ),
    inference(resolution,[status(thm)],[c_205,c_301])).

tff(c_1494,plain,(
    ! [B_845,A_846] :
      ( r2_hidden('#skF_1'('#skF_7',B_845),u1_struct_0(A_846))
      | r1_tarski('#skF_7',B_845)
      | ~ m1_pre_topc('#skF_4',A_846)
      | ~ l1_pre_topc(A_846) ) ),
    inference(resolution,[status(thm)],[c_36,c_1357])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1504,plain,(
    ! [A_847] :
      ( r1_tarski('#skF_7',u1_struct_0(A_847))
      | ~ m1_pre_topc('#skF_4',A_847)
      | ~ l1_pre_topc(A_847) ) ),
    inference(resolution,[status(thm)],[c_1494,c_4])).

tff(c_40,plain,(
    v3_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_326,plain,(
    ! [E_731,B_732,A_733,C_734] :
      ( v3_pre_topc(E_731,B_732)
      | ~ v3_pre_topc(E_731,A_733)
      | ~ r1_tarski(E_731,C_734)
      | ~ r1_tarski(C_734,u1_struct_0(B_732))
      | ~ v3_pre_topc(C_734,A_733)
      | ~ m1_subset_1(E_731,k1_zfmisc_1(u1_struct_0(B_732)))
      | ~ m1_subset_1(E_731,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_subset_1(C_734,k1_zfmisc_1(u1_struct_0(A_733)))
      | ~ m1_pre_topc(B_732,A_733)
      | ~ l1_pre_topc(A_733)
      | ~ v2_pre_topc(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_795,plain,(
    ! [B_787,B_788,A_789] :
      ( v3_pre_topc(B_787,B_788)
      | ~ r1_tarski(B_787,u1_struct_0(B_788))
      | ~ v3_pre_topc(B_787,A_789)
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(B_788)))
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(A_789)))
      | ~ m1_pre_topc(B_788,A_789)
      | ~ l1_pre_topc(A_789)
      | ~ v2_pre_topc(A_789) ) ),
    inference(resolution,[status(thm)],[c_12,c_326])).

tff(c_1392,plain,(
    ! [A_840,B_841,A_842] :
      ( v3_pre_topc(A_840,B_841)
      | ~ v3_pre_topc(A_840,A_842)
      | ~ m1_subset_1(A_840,k1_zfmisc_1(u1_struct_0(A_842)))
      | ~ m1_pre_topc(B_841,A_842)
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | ~ r1_tarski(A_840,u1_struct_0(B_841)) ) ),
    inference(resolution,[status(thm)],[c_16,c_795])).

tff(c_1401,plain,(
    ! [B_841] :
      ( v3_pre_topc('#skF_7',B_841)
      | ~ v3_pre_topc('#skF_7','#skF_3')
      | ~ m1_pre_topc(B_841,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_841)) ) ),
    inference(resolution,[status(thm)],[c_46,c_1392])).

tff(c_1409,plain,(
    ! [B_841] :
      ( v3_pre_topc('#skF_7',B_841)
      | ~ m1_pre_topc(B_841,'#skF_3')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_841)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_40,c_1401])).

tff(c_1562,plain,(
    ! [A_849] :
      ( v3_pre_topc('#skF_7',A_849)
      | ~ m1_pre_topc(A_849,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_849)
      | ~ l1_pre_topc(A_849) ) ),
    inference(resolution,[status(thm)],[c_1504,c_1409])).

tff(c_402,plain,(
    ! [A_737,B_738] :
      ( r2_hidden('#skF_1'(A_737,B_738),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_737,'#skF_7')
      | r1_tarski(A_737,B_738) ) ),
    inference(resolution,[status(thm)],[c_36,c_301])).

tff(c_410,plain,(
    ! [A_737] :
      ( ~ r1_tarski(A_737,'#skF_7')
      | r1_tarski(A_737,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_402,c_4])).

tff(c_818,plain,(
    ! [A_793,B_794,B_795] :
      ( r2_hidden('#skF_1'(A_793,B_794),B_795)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_795)
      | ~ r1_tarski(A_793,'#skF_7')
      | r1_tarski(A_793,B_794) ) ),
    inference(resolution,[status(thm)],[c_402,c_2])).

tff(c_848,plain,(
    ! [B_798,A_799] :
      ( ~ r1_tarski(u1_struct_0('#skF_4'),B_798)
      | ~ r1_tarski(A_799,'#skF_7')
      | r1_tarski(A_799,B_798) ) ),
    inference(resolution,[status(thm)],[c_818,c_4])).

tff(c_961,plain,(
    ! [A_803,A_804] :
      ( ~ r1_tarski(A_803,'#skF_7')
      | r1_tarski(A_803,u1_struct_0(A_804))
      | ~ m1_pre_topc('#skF_4',A_804)
      | ~ l1_pre_topc(A_804) ) ),
    inference(resolution,[status(thm)],[c_205,c_848])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_162,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_207,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_84])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_675,plain,(
    ! [H_777,E_779,F_781,D_782,B_778,C_776,A_780] :
      ( r1_tmap_1(D_782,B_778,E_779,H_777)
      | ~ r1_tmap_1(C_776,B_778,k3_tmap_1(A_780,B_778,D_782,C_776,E_779),H_777)
      | ~ r1_tarski(F_781,u1_struct_0(C_776))
      | ~ r2_hidden(H_777,F_781)
      | ~ v3_pre_topc(F_781,D_782)
      | ~ m1_subset_1(H_777,u1_struct_0(C_776))
      | ~ m1_subset_1(H_777,u1_struct_0(D_782))
      | ~ m1_subset_1(F_781,k1_zfmisc_1(u1_struct_0(D_782)))
      | ~ m1_pre_topc(C_776,D_782)
      | ~ m1_subset_1(E_779,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_782),u1_struct_0(B_778))))
      | ~ v1_funct_2(E_779,u1_struct_0(D_782),u1_struct_0(B_778))
      | ~ v1_funct_1(E_779)
      | ~ m1_pre_topc(D_782,A_780)
      | v2_struct_0(D_782)
      | ~ m1_pre_topc(C_776,A_780)
      | v2_struct_0(C_776)
      | ~ l1_pre_topc(B_778)
      | ~ v2_pre_topc(B_778)
      | v2_struct_0(B_778)
      | ~ l1_pre_topc(A_780)
      | ~ v2_pre_topc(A_780)
      | v2_struct_0(A_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_679,plain,(
    ! [F_781] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_781,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_781)
      | ~ v3_pre_topc(F_781,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_781,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_162,c_675])).

tff(c_686,plain,(
    ! [F_781] :
      ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
      | ~ r1_tarski(F_781,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_781)
      | ~ v3_pre_topc(F_781,'#skF_5')
      | ~ m1_subset_1(F_781,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_72,c_70,c_60,c_56,c_54,c_52,c_50,c_48,c_44,c_85,c_679])).

tff(c_740,plain,(
    ! [F_784] :
      ( ~ r1_tarski(F_784,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_784)
      | ~ v3_pre_topc(F_784,'#skF_5')
      | ~ m1_subset_1(F_784,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_74,c_62,c_58,c_207,c_686])).

tff(c_752,plain,(
    ! [A_8] :
      ( ~ r1_tarski(A_8,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_8)
      | ~ v3_pre_topc(A_8,'#skF_5')
      | ~ r1_tarski(A_8,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_740])).

tff(c_971,plain,(
    ! [A_803] :
      ( ~ r1_tarski(A_803,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_803)
      | ~ v3_pre_topc(A_803,'#skF_5')
      | ~ r1_tarski(A_803,'#skF_7')
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_961,c_752])).

tff(c_1070,plain,(
    ! [A_812] :
      ( ~ r1_tarski(A_812,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_812)
      | ~ v3_pre_topc(A_812,'#skF_5')
      | ~ r1_tarski(A_812,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_48,c_971])).

tff(c_1099,plain,(
    ! [A_737] :
      ( ~ r2_hidden('#skF_8',A_737)
      | ~ v3_pre_topc(A_737,'#skF_5')
      | ~ r1_tarski(A_737,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_410,c_1070])).

tff(c_1566,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1562,c_1099])).

tff(c_1573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_48,c_56,c_12,c_38,c_1566])).

tff(c_1574,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2005,plain,(
    ! [C_905,A_910,D_909,E_908,G_907,B_906] :
      ( r1_tmap_1(D_909,B_906,k3_tmap_1(A_910,B_906,C_905,D_909,E_908),G_907)
      | ~ r1_tmap_1(C_905,B_906,E_908,G_907)
      | ~ m1_pre_topc(D_909,C_905)
      | ~ m1_subset_1(G_907,u1_struct_0(D_909))
      | ~ m1_subset_1(G_907,u1_struct_0(C_905))
      | ~ m1_subset_1(E_908,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_905),u1_struct_0(B_906))))
      | ~ v1_funct_2(E_908,u1_struct_0(C_905),u1_struct_0(B_906))
      | ~ v1_funct_1(E_908)
      | ~ m1_pre_topc(D_909,A_910)
      | v2_struct_0(D_909)
      | ~ m1_pre_topc(C_905,A_910)
      | v2_struct_0(C_905)
      | ~ l1_pre_topc(B_906)
      | ~ v2_pre_topc(B_906)
      | v2_struct_0(B_906)
      | ~ l1_pre_topc(A_910)
      | ~ v2_pre_topc(A_910)
      | v2_struct_0(A_910) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2007,plain,(
    ! [D_909,A_910,G_907] :
      ( r1_tmap_1(D_909,'#skF_2',k3_tmap_1(A_910,'#skF_2','#skF_5',D_909,'#skF_6'),G_907)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_907)
      | ~ m1_pre_topc(D_909,'#skF_5')
      | ~ m1_subset_1(G_907,u1_struct_0(D_909))
      | ~ m1_subset_1(G_907,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_909,A_910)
      | v2_struct_0(D_909)
      | ~ m1_pre_topc('#skF_5',A_910)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_910)
      | ~ v2_pre_topc(A_910)
      | v2_struct_0(A_910) ) ),
    inference(resolution,[status(thm)],[c_50,c_2005])).

tff(c_2013,plain,(
    ! [D_909,A_910,G_907] :
      ( r1_tmap_1(D_909,'#skF_2',k3_tmap_1(A_910,'#skF_2','#skF_5',D_909,'#skF_6'),G_907)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_907)
      | ~ m1_pre_topc(D_909,'#skF_5')
      | ~ m1_subset_1(G_907,u1_struct_0(D_909))
      | ~ m1_subset_1(G_907,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_909,A_910)
      | v2_struct_0(D_909)
      | ~ m1_pre_topc('#skF_5',A_910)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_910)
      | ~ v2_pre_topc(A_910)
      | v2_struct_0(A_910) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_54,c_52,c_2007])).

tff(c_2018,plain,(
    ! [D_911,A_912,G_913] :
      ( r1_tmap_1(D_911,'#skF_2',k3_tmap_1(A_912,'#skF_2','#skF_5',D_911,'#skF_6'),G_913)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',G_913)
      | ~ m1_pre_topc(D_911,'#skF_5')
      | ~ m1_subset_1(G_913,u1_struct_0(D_911))
      | ~ m1_subset_1(G_913,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_911,A_912)
      | v2_struct_0(D_911)
      | ~ m1_pre_topc('#skF_5',A_912)
      | ~ l1_pre_topc(A_912)
      | ~ v2_pre_topc(A_912)
      | v2_struct_0(A_912) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_58,c_2013])).

tff(c_1575,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2021,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2018,c_1575])).

tff(c_2024,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_56,c_60,c_44,c_85,c_48,c_1574,c_2021])).

tff(c_2026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.91/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.87  
% 4.91/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.87  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.91/1.87  
% 4.91/1.87  %Foreground sorts:
% 4.91/1.87  
% 4.91/1.87  
% 4.91/1.87  %Background operators:
% 4.91/1.87  
% 4.91/1.87  
% 4.91/1.87  %Foreground operators:
% 4.91/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.91/1.87  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.91/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.91/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.91/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.91/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.91/1.87  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.91/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.91/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.91/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.91/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.91/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.91/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.91/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.91/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.91/1.87  tff('#skF_9', type, '#skF_9': $i).
% 4.91/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.91/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.91/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.91/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.91/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.91/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.91/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.91/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.91/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.91/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.91/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.91/1.87  
% 4.91/1.89  tff(f_259, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.91/1.89  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.91/1.89  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.91/1.89  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.91/1.89  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.91/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.91/1.89  tff(f_201, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => ((((v3_pre_topc(C, A) & r1_tarski(C, u1_struct_0(B))) & r1_tarski(D, C)) & (D = E)) => (v3_pre_topc(E, B) <=> v3_pre_topc(D, A))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tsep_1)).
% 4.91/1.89  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.91/1.89  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.91/1.89  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_34, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_42, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 4.91/1.89  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_102, plain, (![B_688, A_689]: (l1_pre_topc(B_688) | ~m1_pre_topc(B_688, A_689) | ~l1_pre_topc(A_689))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.91/1.89  tff(c_111, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_102])).
% 4.91/1.89  tff(c_118, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_111])).
% 4.91/1.89  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.91/1.89  tff(c_38, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_36, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_201, plain, (![B_704, A_705]: (m1_subset_1(u1_struct_0(B_704), k1_zfmisc_1(u1_struct_0(A_705))) | ~m1_pre_topc(B_704, A_705) | ~l1_pre_topc(A_705))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.91/1.89  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.91/1.89  tff(c_205, plain, (![B_704, A_705]: (r1_tarski(u1_struct_0(B_704), u1_struct_0(A_705)) | ~m1_pre_topc(B_704, A_705) | ~l1_pre_topc(A_705))), inference(resolution, [status(thm)], [c_201, c_14])).
% 4.91/1.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.91/1.89  tff(c_150, plain, (![C_696, B_697, A_698]: (r2_hidden(C_696, B_697) | ~r2_hidden(C_696, A_698) | ~r1_tarski(A_698, B_697))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.91/1.89  tff(c_233, plain, (![A_710, B_711, B_712]: (r2_hidden('#skF_1'(A_710, B_711), B_712) | ~r1_tarski(A_710, B_712) | r1_tarski(A_710, B_711))), inference(resolution, [status(thm)], [c_6, c_150])).
% 4.91/1.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.91/1.89  tff(c_301, plain, (![A_725, B_726, B_727, B_728]: (r2_hidden('#skF_1'(A_725, B_726), B_727) | ~r1_tarski(B_728, B_727) | ~r1_tarski(A_725, B_728) | r1_tarski(A_725, B_726))), inference(resolution, [status(thm)], [c_233, c_2])).
% 4.91/1.89  tff(c_1357, plain, (![A_834, B_835, A_836, B_837]: (r2_hidden('#skF_1'(A_834, B_835), u1_struct_0(A_836)) | ~r1_tarski(A_834, u1_struct_0(B_837)) | r1_tarski(A_834, B_835) | ~m1_pre_topc(B_837, A_836) | ~l1_pre_topc(A_836))), inference(resolution, [status(thm)], [c_205, c_301])).
% 4.91/1.89  tff(c_1494, plain, (![B_845, A_846]: (r2_hidden('#skF_1'('#skF_7', B_845), u1_struct_0(A_846)) | r1_tarski('#skF_7', B_845) | ~m1_pre_topc('#skF_4', A_846) | ~l1_pre_topc(A_846))), inference(resolution, [status(thm)], [c_36, c_1357])).
% 4.91/1.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.91/1.89  tff(c_1504, plain, (![A_847]: (r1_tarski('#skF_7', u1_struct_0(A_847)) | ~m1_pre_topc('#skF_4', A_847) | ~l1_pre_topc(A_847))), inference(resolution, [status(thm)], [c_1494, c_4])).
% 4.91/1.89  tff(c_40, plain, (v3_pre_topc('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.91/1.89  tff(c_326, plain, (![E_731, B_732, A_733, C_734]: (v3_pre_topc(E_731, B_732) | ~v3_pre_topc(E_731, A_733) | ~r1_tarski(E_731, C_734) | ~r1_tarski(C_734, u1_struct_0(B_732)) | ~v3_pre_topc(C_734, A_733) | ~m1_subset_1(E_731, k1_zfmisc_1(u1_struct_0(B_732))) | ~m1_subset_1(E_731, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_subset_1(C_734, k1_zfmisc_1(u1_struct_0(A_733))) | ~m1_pre_topc(B_732, A_733) | ~l1_pre_topc(A_733) | ~v2_pre_topc(A_733))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.91/1.89  tff(c_795, plain, (![B_787, B_788, A_789]: (v3_pre_topc(B_787, B_788) | ~r1_tarski(B_787, u1_struct_0(B_788)) | ~v3_pre_topc(B_787, A_789) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(B_788))) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(A_789))) | ~m1_pre_topc(B_788, A_789) | ~l1_pre_topc(A_789) | ~v2_pre_topc(A_789))), inference(resolution, [status(thm)], [c_12, c_326])).
% 4.91/1.89  tff(c_1392, plain, (![A_840, B_841, A_842]: (v3_pre_topc(A_840, B_841) | ~v3_pre_topc(A_840, A_842) | ~m1_subset_1(A_840, k1_zfmisc_1(u1_struct_0(A_842))) | ~m1_pre_topc(B_841, A_842) | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | ~r1_tarski(A_840, u1_struct_0(B_841)))), inference(resolution, [status(thm)], [c_16, c_795])).
% 4.91/1.89  tff(c_1401, plain, (![B_841]: (v3_pre_topc('#skF_7', B_841) | ~v3_pre_topc('#skF_7', '#skF_3') | ~m1_pre_topc(B_841, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski('#skF_7', u1_struct_0(B_841)))), inference(resolution, [status(thm)], [c_46, c_1392])).
% 4.91/1.89  tff(c_1409, plain, (![B_841]: (v3_pre_topc('#skF_7', B_841) | ~m1_pre_topc(B_841, '#skF_3') | ~r1_tarski('#skF_7', u1_struct_0(B_841)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_40, c_1401])).
% 4.91/1.89  tff(c_1562, plain, (![A_849]: (v3_pre_topc('#skF_7', A_849) | ~m1_pre_topc(A_849, '#skF_3') | ~m1_pre_topc('#skF_4', A_849) | ~l1_pre_topc(A_849))), inference(resolution, [status(thm)], [c_1504, c_1409])).
% 4.91/1.89  tff(c_402, plain, (![A_737, B_738]: (r2_hidden('#skF_1'(A_737, B_738), u1_struct_0('#skF_4')) | ~r1_tarski(A_737, '#skF_7') | r1_tarski(A_737, B_738))), inference(resolution, [status(thm)], [c_36, c_301])).
% 4.91/1.89  tff(c_410, plain, (![A_737]: (~r1_tarski(A_737, '#skF_7') | r1_tarski(A_737, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_402, c_4])).
% 4.91/1.89  tff(c_818, plain, (![A_793, B_794, B_795]: (r2_hidden('#skF_1'(A_793, B_794), B_795) | ~r1_tarski(u1_struct_0('#skF_4'), B_795) | ~r1_tarski(A_793, '#skF_7') | r1_tarski(A_793, B_794))), inference(resolution, [status(thm)], [c_402, c_2])).
% 4.91/1.89  tff(c_848, plain, (![B_798, A_799]: (~r1_tarski(u1_struct_0('#skF_4'), B_798) | ~r1_tarski(A_799, '#skF_7') | r1_tarski(A_799, B_798))), inference(resolution, [status(thm)], [c_818, c_4])).
% 4.91/1.89  tff(c_961, plain, (![A_803, A_804]: (~r1_tarski(A_803, '#skF_7') | r1_tarski(A_803, u1_struct_0(A_804)) | ~m1_pre_topc('#skF_4', A_804) | ~l1_pre_topc(A_804))), inference(resolution, [status(thm)], [c_205, c_848])).
% 4.91/1.89  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_82, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_83, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 4.91/1.89  tff(c_162, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 4.91/1.89  tff(c_76, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_84, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 4.91/1.89  tff(c_207, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_84])).
% 4.91/1.89  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_259])).
% 4.91/1.89  tff(c_675, plain, (![H_777, E_779, F_781, D_782, B_778, C_776, A_780]: (r1_tmap_1(D_782, B_778, E_779, H_777) | ~r1_tmap_1(C_776, B_778, k3_tmap_1(A_780, B_778, D_782, C_776, E_779), H_777) | ~r1_tarski(F_781, u1_struct_0(C_776)) | ~r2_hidden(H_777, F_781) | ~v3_pre_topc(F_781, D_782) | ~m1_subset_1(H_777, u1_struct_0(C_776)) | ~m1_subset_1(H_777, u1_struct_0(D_782)) | ~m1_subset_1(F_781, k1_zfmisc_1(u1_struct_0(D_782))) | ~m1_pre_topc(C_776, D_782) | ~m1_subset_1(E_779, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_782), u1_struct_0(B_778)))) | ~v1_funct_2(E_779, u1_struct_0(D_782), u1_struct_0(B_778)) | ~v1_funct_1(E_779) | ~m1_pre_topc(D_782, A_780) | v2_struct_0(D_782) | ~m1_pre_topc(C_776, A_780) | v2_struct_0(C_776) | ~l1_pre_topc(B_778) | ~v2_pre_topc(B_778) | v2_struct_0(B_778) | ~l1_pre_topc(A_780) | ~v2_pre_topc(A_780) | v2_struct_0(A_780))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.91/1.89  tff(c_679, plain, (![F_781]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_781, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_781) | ~v3_pre_topc(F_781, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_781, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_162, c_675])).
% 4.91/1.89  tff(c_686, plain, (![F_781]: (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~r1_tarski(F_781, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_781) | ~v3_pre_topc(F_781, '#skF_5') | ~m1_subset_1(F_781, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_72, c_70, c_60, c_56, c_54, c_52, c_50, c_48, c_44, c_85, c_679])).
% 4.91/1.89  tff(c_740, plain, (![F_784]: (~r1_tarski(F_784, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_784) | ~v3_pre_topc(F_784, '#skF_5') | ~m1_subset_1(F_784, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_74, c_62, c_58, c_207, c_686])).
% 4.91/1.89  tff(c_752, plain, (![A_8]: (~r1_tarski(A_8, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_8) | ~v3_pre_topc(A_8, '#skF_5') | ~r1_tarski(A_8, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_740])).
% 4.91/1.89  tff(c_971, plain, (![A_803]: (~r1_tarski(A_803, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_803) | ~v3_pre_topc(A_803, '#skF_5') | ~r1_tarski(A_803, '#skF_7') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_961, c_752])).
% 4.91/1.89  tff(c_1070, plain, (![A_812]: (~r1_tarski(A_812, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_812) | ~v3_pre_topc(A_812, '#skF_5') | ~r1_tarski(A_812, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_48, c_971])).
% 4.91/1.89  tff(c_1099, plain, (![A_737]: (~r2_hidden('#skF_8', A_737) | ~v3_pre_topc(A_737, '#skF_5') | ~r1_tarski(A_737, '#skF_7'))), inference(resolution, [status(thm)], [c_410, c_1070])).
% 4.91/1.89  tff(c_1566, plain, (~r2_hidden('#skF_8', '#skF_7') | ~r1_tarski('#skF_7', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1562, c_1099])).
% 4.91/1.89  tff(c_1573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_48, c_56, c_12, c_38, c_1566])).
% 4.91/1.89  tff(c_1574, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 4.91/1.89  tff(c_2005, plain, (![C_905, A_910, D_909, E_908, G_907, B_906]: (r1_tmap_1(D_909, B_906, k3_tmap_1(A_910, B_906, C_905, D_909, E_908), G_907) | ~r1_tmap_1(C_905, B_906, E_908, G_907) | ~m1_pre_topc(D_909, C_905) | ~m1_subset_1(G_907, u1_struct_0(D_909)) | ~m1_subset_1(G_907, u1_struct_0(C_905)) | ~m1_subset_1(E_908, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_905), u1_struct_0(B_906)))) | ~v1_funct_2(E_908, u1_struct_0(C_905), u1_struct_0(B_906)) | ~v1_funct_1(E_908) | ~m1_pre_topc(D_909, A_910) | v2_struct_0(D_909) | ~m1_pre_topc(C_905, A_910) | v2_struct_0(C_905) | ~l1_pre_topc(B_906) | ~v2_pre_topc(B_906) | v2_struct_0(B_906) | ~l1_pre_topc(A_910) | ~v2_pre_topc(A_910) | v2_struct_0(A_910))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.91/1.89  tff(c_2007, plain, (![D_909, A_910, G_907]: (r1_tmap_1(D_909, '#skF_2', k3_tmap_1(A_910, '#skF_2', '#skF_5', D_909, '#skF_6'), G_907) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_907) | ~m1_pre_topc(D_909, '#skF_5') | ~m1_subset_1(G_907, u1_struct_0(D_909)) | ~m1_subset_1(G_907, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_909, A_910) | v2_struct_0(D_909) | ~m1_pre_topc('#skF_5', A_910) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_910) | ~v2_pre_topc(A_910) | v2_struct_0(A_910))), inference(resolution, [status(thm)], [c_50, c_2005])).
% 4.91/1.89  tff(c_2013, plain, (![D_909, A_910, G_907]: (r1_tmap_1(D_909, '#skF_2', k3_tmap_1(A_910, '#skF_2', '#skF_5', D_909, '#skF_6'), G_907) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_907) | ~m1_pre_topc(D_909, '#skF_5') | ~m1_subset_1(G_907, u1_struct_0(D_909)) | ~m1_subset_1(G_907, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_909, A_910) | v2_struct_0(D_909) | ~m1_pre_topc('#skF_5', A_910) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_910) | ~v2_pre_topc(A_910) | v2_struct_0(A_910))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_54, c_52, c_2007])).
% 4.91/1.89  tff(c_2018, plain, (![D_911, A_912, G_913]: (r1_tmap_1(D_911, '#skF_2', k3_tmap_1(A_912, '#skF_2', '#skF_5', D_911, '#skF_6'), G_913) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', G_913) | ~m1_pre_topc(D_911, '#skF_5') | ~m1_subset_1(G_913, u1_struct_0(D_911)) | ~m1_subset_1(G_913, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_911, A_912) | v2_struct_0(D_911) | ~m1_pre_topc('#skF_5', A_912) | ~l1_pre_topc(A_912) | ~v2_pre_topc(A_912) | v2_struct_0(A_912))), inference(negUnitSimplification, [status(thm)], [c_74, c_58, c_2013])).
% 4.91/1.89  tff(c_1575, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 4.91/1.89  tff(c_2021, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2018, c_1575])).
% 4.91/1.89  tff(c_2024, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_56, c_60, c_44, c_85, c_48, c_1574, c_2021])).
% 4.91/1.89  tff(c_2026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2024])).
% 4.91/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.91/1.89  
% 4.91/1.89  Inference rules
% 4.91/1.89  ----------------------
% 4.91/1.89  #Ref     : 0
% 4.91/1.89  #Sup     : 415
% 4.91/1.89  #Fact    : 0
% 4.91/1.89  #Define  : 0
% 4.91/1.89  #Split   : 21
% 4.91/1.89  #Chain   : 0
% 4.91/1.89  #Close   : 0
% 4.91/1.89  
% 4.91/1.89  Ordering : KBO
% 4.91/1.89  
% 4.91/1.89  Simplification rules
% 4.91/1.89  ----------------------
% 4.91/1.89  #Subsume      : 155
% 4.91/1.89  #Demod        : 195
% 4.91/1.89  #Tautology    : 45
% 4.91/1.89  #SimpNegUnit  : 7
% 4.91/1.89  #BackRed      : 0
% 4.91/1.89  
% 4.91/1.89  #Partial instantiations: 0
% 4.91/1.89  #Strategies tried      : 1
% 4.91/1.89  
% 4.91/1.89  Timing (in seconds)
% 4.91/1.89  ----------------------
% 4.91/1.90  Preprocessing        : 0.42
% 4.91/1.90  Parsing              : 0.21
% 4.91/1.90  CNF conversion       : 0.07
% 4.91/1.90  Main loop            : 0.68
% 4.91/1.90  Inferencing          : 0.21
% 4.91/1.90  Reduction            : 0.21
% 4.91/1.90  Demodulation         : 0.15
% 4.91/1.90  BG Simplification    : 0.03
% 4.91/1.90  Subsumption          : 0.19
% 4.91/1.90  Abstraction          : 0.03
% 4.91/1.90  MUC search           : 0.00
% 4.91/1.90  Cooper               : 0.00
% 4.91/1.90  Total                : 1.14
% 4.91/1.90  Index Insertion      : 0.00
% 4.91/1.90  Index Deletion       : 0.00
% 4.91/1.90  Index Matching       : 0.00
% 4.91/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
