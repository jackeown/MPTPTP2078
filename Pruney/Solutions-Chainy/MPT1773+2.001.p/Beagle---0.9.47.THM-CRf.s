%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 445 expanded)
%              Number of leaves         :   42 ( 191 expanded)
%              Depth                    :   17
%              Number of atoms          :  495 (3927 expanded)
%              Number of equality atoms :   33 ( 191 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff(f_325,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_160,axiom,(
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

tff(f_128,axiom,(
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

tff(f_267,axiom,(
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

tff(f_200,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_38,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_89,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_40,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_134,plain,(
    ! [B_662,A_663] :
      ( v2_pre_topc(B_662)
      | ~ m1_pre_topc(B_662,A_663)
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_134])).

tff(c_149,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_140])).

tff(c_96,plain,(
    ! [B_654,A_655] :
      ( l1_pre_topc(B_654)
      | ~ m1_pre_topc(B_654,A_655)
      | ~ l1_pre_topc(A_655) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_96])).

tff(c_109,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_102])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_378,plain,(
    ! [B_705,A_706,C_707] :
      ( r1_tarski(B_705,k1_tops_1(A_706,C_707))
      | ~ r1_tarski(B_705,C_707)
      | ~ v3_pre_topc(B_705,A_706)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ m1_subset_1(B_705,k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ l1_pre_topc(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_380,plain,(
    ! [B_705] :
      ( r1_tarski(B_705,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(B_705,'#skF_7')
      | ~ v3_pre_topc(B_705,'#skF_5')
      | ~ m1_subset_1(B_705,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_378])).

tff(c_391,plain,(
    ! [B_708] :
      ( r1_tarski(B_708,k1_tops_1('#skF_5','#skF_7'))
      | ~ r1_tarski(B_708,'#skF_7')
      | ~ v3_pre_topc(B_708,'#skF_5')
      | ~ m1_subset_1(B_708,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_380])).

tff(c_394,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_391])).

tff(c_397,plain,(
    r1_tarski('#skF_7',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12,c_394])).

tff(c_42,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_155,plain,(
    ! [C_664,B_665,A_666] :
      ( r2_hidden(C_664,B_665)
      | ~ r2_hidden(C_664,A_666)
      | ~ r1_tarski(A_666,B_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [B_667] :
      ( r2_hidden('#skF_8',B_667)
      | ~ r1_tarski('#skF_7',B_667) ) ),
    inference(resolution,[status(thm)],[c_42,c_155])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [B_2,B_667] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_667,B_2)
      | ~ r1_tarski('#skF_7',B_667) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_403,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_397,c_165])).

tff(c_410,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_403])).

tff(c_429,plain,(
    ! [C_710,A_711,B_712] :
      ( m1_connsp_2(C_710,A_711,B_712)
      | ~ r2_hidden(B_712,k1_tops_1(A_711,C_710))
      | ~ m1_subset_1(C_710,k1_zfmisc_1(u1_struct_0(A_711)))
      | ~ m1_subset_1(B_712,u1_struct_0(A_711))
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_431,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_410,c_429])).

tff(c_446,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_109,c_48,c_50,c_431])).

tff(c_447,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_446])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_87,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_86])).

tff(c_178,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_88,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_213,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_88])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_723,plain,(
    ! [E_768,A_767,C_770,B_771,D_769] :
      ( k3_tmap_1(A_767,B_771,C_770,D_769,E_768) = k2_partfun1(u1_struct_0(C_770),u1_struct_0(B_771),E_768,u1_struct_0(D_769))
      | ~ m1_pre_topc(D_769,C_770)
      | ~ m1_subset_1(E_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_770),u1_struct_0(B_771))))
      | ~ v1_funct_2(E_768,u1_struct_0(C_770),u1_struct_0(B_771))
      | ~ v1_funct_1(E_768)
      | ~ m1_pre_topc(D_769,A_767)
      | ~ m1_pre_topc(C_770,A_767)
      | ~ l1_pre_topc(B_771)
      | ~ v2_pre_topc(B_771)
      | v2_struct_0(B_771)
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_725,plain,(
    ! [A_767,D_769] :
      ( k3_tmap_1(A_767,'#skF_3','#skF_5',D_769,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_769))
      | ~ m1_pre_topc(D_769,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_769,A_767)
      | ~ m1_pre_topc('#skF_5',A_767)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(resolution,[status(thm)],[c_54,c_723])).

tff(c_728,plain,(
    ! [A_767,D_769] :
      ( k3_tmap_1(A_767,'#skF_3','#skF_5',D_769,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_769))
      | ~ m1_pre_topc(D_769,'#skF_5')
      | ~ m1_pre_topc(D_769,A_767)
      | ~ m1_pre_topc('#skF_5',A_767)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_725])).

tff(c_730,plain,(
    ! [A_772,D_773] :
      ( k3_tmap_1(A_772,'#skF_3','#skF_5',D_773,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_773))
      | ~ m1_pre_topc(D_773,'#skF_5')
      | ~ m1_pre_topc(D_773,A_772)
      | ~ m1_pre_topc('#skF_5',A_772)
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772)
      | v2_struct_0(A_772) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_728])).

tff(c_738,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_730])).

tff(c_750,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_52,c_738])).

tff(c_751,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_750])).

tff(c_647,plain,(
    ! [A_740,B_741,C_742,D_743] :
      ( k2_partfun1(u1_struct_0(A_740),u1_struct_0(B_741),C_742,u1_struct_0(D_743)) = k2_tmap_1(A_740,B_741,C_742,D_743)
      | ~ m1_pre_topc(D_743,A_740)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_740),u1_struct_0(B_741))))
      | ~ v1_funct_2(C_742,u1_struct_0(A_740),u1_struct_0(B_741))
      | ~ v1_funct_1(C_742)
      | ~ l1_pre_topc(B_741)
      | ~ v2_pre_topc(B_741)
      | v2_struct_0(B_741)
      | ~ l1_pre_topc(A_740)
      | ~ v2_pre_topc(A_740)
      | v2_struct_0(A_740) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_649,plain,(
    ! [D_743] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_743)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_743)
      | ~ m1_pre_topc(D_743,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_647])).

tff(c_652,plain,(
    ! [D_743] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_743)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_743)
      | ~ m1_pre_topc(D_743,'#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_109,c_70,c_68,c_58,c_56,c_649])).

tff(c_653,plain,(
    ! [D_743] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_743)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_743)
      | ~ m1_pre_topc(D_743,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_72,c_652])).

tff(c_755,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_653])).

tff(c_762,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_755])).

tff(c_767,plain,(
    r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_178])).

tff(c_812,plain,(
    ! [E_799,D_798,A_802,C_796,B_800,F_797,H_801] :
      ( r1_tmap_1(D_798,B_800,E_799,H_801)
      | ~ r1_tmap_1(C_796,B_800,k3_tmap_1(A_802,B_800,D_798,C_796,E_799),H_801)
      | ~ m1_connsp_2(F_797,D_798,H_801)
      | ~ r1_tarski(F_797,u1_struct_0(C_796))
      | ~ m1_subset_1(H_801,u1_struct_0(C_796))
      | ~ m1_subset_1(H_801,u1_struct_0(D_798))
      | ~ m1_subset_1(F_797,k1_zfmisc_1(u1_struct_0(D_798)))
      | ~ m1_pre_topc(C_796,D_798)
      | ~ m1_subset_1(E_799,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_798),u1_struct_0(B_800))))
      | ~ v1_funct_2(E_799,u1_struct_0(D_798),u1_struct_0(B_800))
      | ~ v1_funct_1(E_799)
      | ~ m1_pre_topc(D_798,A_802)
      | v2_struct_0(D_798)
      | ~ m1_pre_topc(C_796,A_802)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_800)
      | ~ v2_pre_topc(B_800)
      | v2_struct_0(B_800)
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_814,plain,(
    ! [H_801,F_797] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6',H_801)
      | ~ r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),H_801)
      | ~ m1_connsp_2(F_797,'#skF_5',H_801)
      | ~ r1_tarski(F_797,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_801,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_801,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_797,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(superposition,[status(thm),theory(equality)],[c_762,c_812])).

tff(c_816,plain,(
    ! [H_801,F_797] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6',H_801)
      | ~ r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),H_801)
      | ~ m1_connsp_2(F_797,'#skF_5',H_801)
      | ~ r1_tarski(F_797,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_801,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_801,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_797,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_56,c_54,c_52,c_814])).

tff(c_818,plain,(
    ! [H_803,F_804] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6',H_803)
      | ~ r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),H_803)
      | ~ m1_connsp_2(F_804,'#skF_5',H_803)
      | ~ r1_tarski(F_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_803,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_803,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_804,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_816])).

tff(c_823,plain,(
    ! [F_804] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_804,'#skF_5','#skF_8')
      | ~ r1_tarski(F_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_804,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_767,c_818])).

tff(c_830,plain,(
    ! [F_804] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_804,'#skF_5','#skF_8')
      | ~ r1_tarski(F_804,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_804,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_89,c_823])).

tff(c_832,plain,(
    ! [F_805] :
      ( ~ m1_connsp_2(F_805,'#skF_5','#skF_8')
      | ~ r1_tarski(F_805,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_805,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_830])).

tff(c_835,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_5','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_832])).

tff(c_839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_447,c_835])).

tff(c_840,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_1453,plain,(
    ! [F_914,A_915,D_918,B_917,C_916] :
      ( r1_tmap_1(D_918,A_915,k2_tmap_1(B_917,A_915,C_916,D_918),F_914)
      | ~ r1_tmap_1(B_917,A_915,C_916,F_914)
      | ~ m1_subset_1(F_914,u1_struct_0(D_918))
      | ~ m1_subset_1(F_914,u1_struct_0(B_917))
      | ~ m1_pre_topc(D_918,B_917)
      | v2_struct_0(D_918)
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_917),u1_struct_0(A_915))))
      | ~ v1_funct_2(C_916,u1_struct_0(B_917),u1_struct_0(A_915))
      | ~ v1_funct_1(C_916)
      | ~ l1_pre_topc(B_917)
      | ~ v2_pre_topc(B_917)
      | v2_struct_0(B_917)
      | ~ l1_pre_topc(A_915)
      | ~ v2_pre_topc(A_915)
      | v2_struct_0(A_915) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1455,plain,(
    ! [D_918,F_914] :
      ( r1_tmap_1(D_918,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_918),F_914)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_914)
      | ~ m1_subset_1(F_914,u1_struct_0(D_918))
      | ~ m1_subset_1(F_914,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_918,'#skF_5')
      | v2_struct_0(D_918)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_1453])).

tff(c_1458,plain,(
    ! [D_918,F_914] :
      ( r1_tmap_1(D_918,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_918),F_914)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_914)
      | ~ m1_subset_1(F_914,u1_struct_0(D_918))
      | ~ m1_subset_1(F_914,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_918,'#skF_5')
      | v2_struct_0(D_918)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_149,c_109,c_58,c_56,c_1455])).

tff(c_1460,plain,(
    ! [D_919,F_920] :
      ( r1_tmap_1(D_919,'#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6',D_919),F_920)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',F_920)
      | ~ m1_subset_1(F_920,u1_struct_0(D_919))
      | ~ m1_subset_1(F_920,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_919,'#skF_5')
      | v2_struct_0(D_919) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_1458])).

tff(c_1386,plain,(
    ! [A_903,B_907,C_906,E_904,D_905] :
      ( k3_tmap_1(A_903,B_907,C_906,D_905,E_904) = k2_partfun1(u1_struct_0(C_906),u1_struct_0(B_907),E_904,u1_struct_0(D_905))
      | ~ m1_pre_topc(D_905,C_906)
      | ~ m1_subset_1(E_904,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_906),u1_struct_0(B_907))))
      | ~ v1_funct_2(E_904,u1_struct_0(C_906),u1_struct_0(B_907))
      | ~ v1_funct_1(E_904)
      | ~ m1_pre_topc(D_905,A_903)
      | ~ m1_pre_topc(C_906,A_903)
      | ~ l1_pre_topc(B_907)
      | ~ v2_pre_topc(B_907)
      | v2_struct_0(B_907)
      | ~ l1_pre_topc(A_903)
      | ~ v2_pre_topc(A_903)
      | v2_struct_0(A_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1388,plain,(
    ! [A_903,D_905] :
      ( k3_tmap_1(A_903,'#skF_3','#skF_5',D_905,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_905))
      | ~ m1_pre_topc(D_905,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_905,A_903)
      | ~ m1_pre_topc('#skF_5',A_903)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_903)
      | ~ v2_pre_topc(A_903)
      | v2_struct_0(A_903) ) ),
    inference(resolution,[status(thm)],[c_54,c_1386])).

tff(c_1391,plain,(
    ! [A_903,D_905] :
      ( k3_tmap_1(A_903,'#skF_3','#skF_5',D_905,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_905))
      | ~ m1_pre_topc(D_905,'#skF_5')
      | ~ m1_pre_topc(D_905,A_903)
      | ~ m1_pre_topc('#skF_5',A_903)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_903)
      | ~ v2_pre_topc(A_903)
      | v2_struct_0(A_903) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_56,c_1388])).

tff(c_1393,plain,(
    ! [A_908,D_909] :
      ( k3_tmap_1(A_908,'#skF_3','#skF_5',D_909,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_909))
      | ~ m1_pre_topc(D_909,'#skF_5')
      | ~ m1_pre_topc(D_909,A_908)
      | ~ m1_pre_topc('#skF_5',A_908)
      | ~ l1_pre_topc(A_908)
      | ~ v2_pre_topc(A_908)
      | v2_struct_0(A_908) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1391])).

tff(c_1401,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1393])).

tff(c_1413,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_52,c_1401])).

tff(c_1414,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1413])).

tff(c_1310,plain,(
    ! [A_876,B_877,C_878,D_879] :
      ( k2_partfun1(u1_struct_0(A_876),u1_struct_0(B_877),C_878,u1_struct_0(D_879)) = k2_tmap_1(A_876,B_877,C_878,D_879)
      | ~ m1_pre_topc(D_879,A_876)
      | ~ m1_subset_1(C_878,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_876),u1_struct_0(B_877))))
      | ~ v1_funct_2(C_878,u1_struct_0(A_876),u1_struct_0(B_877))
      | ~ v1_funct_1(C_878)
      | ~ l1_pre_topc(B_877)
      | ~ v2_pre_topc(B_877)
      | v2_struct_0(B_877)
      | ~ l1_pre_topc(A_876)
      | ~ v2_pre_topc(A_876)
      | v2_struct_0(A_876) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1312,plain,(
    ! [D_879] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_879)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_879)
      | ~ m1_pre_topc(D_879,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1310])).

tff(c_1315,plain,(
    ! [D_879] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_879)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_879)
      | ~ m1_pre_topc(D_879,'#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_109,c_70,c_68,c_58,c_56,c_1312])).

tff(c_1316,plain,(
    ! [D_879] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_879)) = k2_tmap_1('#skF_5','#skF_3','#skF_6',D_879)
      | ~ m1_pre_topc(D_879,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_72,c_1315])).

tff(c_1418,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1414,c_1316])).

tff(c_1425,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1418])).

tff(c_841,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_1430,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k2_tmap_1('#skF_5','#skF_3','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_841])).

tff(c_1463,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1460,c_1430])).

tff(c_1466,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_89,c_840,c_1463])).

tff(c_1468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.88  
% 4.68/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.89  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.68/1.89  
% 4.68/1.89  %Foreground sorts:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Background operators:
% 4.68/1.89  
% 4.68/1.89  
% 4.68/1.89  %Foreground operators:
% 4.68/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.89  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.68/1.89  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.89  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.68/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.89  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.68/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.68/1.89  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.68/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.89  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.68/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.89  
% 4.68/1.91  tff(f_325, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.68/1.91  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.68/1.91  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.68/1.91  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.91  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.68/1.91  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.68/1.91  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.68/1.91  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.68/1.91  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.68/1.91  tff(f_267, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.68/1.91  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.68/1.91  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_38, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_89, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 4.68/1.91  tff(c_40, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_134, plain, (![B_662, A_663]: (v2_pre_topc(B_662) | ~m1_pre_topc(B_662, A_663) | ~l1_pre_topc(A_663) | ~v2_pre_topc(A_663))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.91  tff(c_140, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_134])).
% 4.68/1.91  tff(c_149, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_140])).
% 4.68/1.91  tff(c_96, plain, (![B_654, A_655]: (l1_pre_topc(B_654) | ~m1_pre_topc(B_654, A_655) | ~l1_pre_topc(A_655))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.68/1.91  tff(c_102, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_96])).
% 4.68/1.91  tff(c_109, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_102])).
% 4.68/1.91  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.68/1.91  tff(c_44, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_378, plain, (![B_705, A_706, C_707]: (r1_tarski(B_705, k1_tops_1(A_706, C_707)) | ~r1_tarski(B_705, C_707) | ~v3_pre_topc(B_705, A_706) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0(A_706))) | ~m1_subset_1(B_705, k1_zfmisc_1(u1_struct_0(A_706))) | ~l1_pre_topc(A_706))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.68/1.91  tff(c_380, plain, (![B_705]: (r1_tarski(B_705, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(B_705, '#skF_7') | ~v3_pre_topc(B_705, '#skF_5') | ~m1_subset_1(B_705, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_378])).
% 4.68/1.91  tff(c_391, plain, (![B_708]: (r1_tarski(B_708, k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski(B_708, '#skF_7') | ~v3_pre_topc(B_708, '#skF_5') | ~m1_subset_1(B_708, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_380])).
% 4.68/1.91  tff(c_394, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_391])).
% 4.68/1.91  tff(c_397, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12, c_394])).
% 4.68/1.91  tff(c_42, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_155, plain, (![C_664, B_665, A_666]: (r2_hidden(C_664, B_665) | ~r2_hidden(C_664, A_666) | ~r1_tarski(A_666, B_665))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.91  tff(c_162, plain, (![B_667]: (r2_hidden('#skF_8', B_667) | ~r1_tarski('#skF_7', B_667))), inference(resolution, [status(thm)], [c_42, c_155])).
% 4.68/1.91  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.91  tff(c_165, plain, (![B_2, B_667]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_667, B_2) | ~r1_tarski('#skF_7', B_667))), inference(resolution, [status(thm)], [c_162, c_2])).
% 4.68/1.91  tff(c_403, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_397, c_165])).
% 4.68/1.91  tff(c_410, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_403])).
% 4.68/1.91  tff(c_429, plain, (![C_710, A_711, B_712]: (m1_connsp_2(C_710, A_711, B_712) | ~r2_hidden(B_712, k1_tops_1(A_711, C_710)) | ~m1_subset_1(C_710, k1_zfmisc_1(u1_struct_0(A_711))) | ~m1_subset_1(B_712, u1_struct_0(A_711)) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.68/1.91  tff(c_431, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_410, c_429])).
% 4.68/1.91  tff(c_446, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_109, c_48, c_50, c_431])).
% 4.68/1.91  tff(c_447, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_446])).
% 4.68/1.91  tff(c_86, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_87, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_86])).
% 4.68/1.91  tff(c_178, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 4.68/1.91  tff(c_80, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_88, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 4.68/1.91  tff(c_213, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_88])).
% 4.68/1.91  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.68/1.91  tff(c_723, plain, (![E_768, A_767, C_770, B_771, D_769]: (k3_tmap_1(A_767, B_771, C_770, D_769, E_768)=k2_partfun1(u1_struct_0(C_770), u1_struct_0(B_771), E_768, u1_struct_0(D_769)) | ~m1_pre_topc(D_769, C_770) | ~m1_subset_1(E_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_770), u1_struct_0(B_771)))) | ~v1_funct_2(E_768, u1_struct_0(C_770), u1_struct_0(B_771)) | ~v1_funct_1(E_768) | ~m1_pre_topc(D_769, A_767) | ~m1_pre_topc(C_770, A_767) | ~l1_pre_topc(B_771) | ~v2_pre_topc(B_771) | v2_struct_0(B_771) | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.68/1.91  tff(c_725, plain, (![A_767, D_769]: (k3_tmap_1(A_767, '#skF_3', '#skF_5', D_769, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_769)) | ~m1_pre_topc(D_769, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_769, A_767) | ~m1_pre_topc('#skF_5', A_767) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(resolution, [status(thm)], [c_54, c_723])).
% 4.68/1.91  tff(c_728, plain, (![A_767, D_769]: (k3_tmap_1(A_767, '#skF_3', '#skF_5', D_769, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_769)) | ~m1_pre_topc(D_769, '#skF_5') | ~m1_pre_topc(D_769, A_767) | ~m1_pre_topc('#skF_5', A_767) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_725])).
% 4.68/1.91  tff(c_730, plain, (![A_772, D_773]: (k3_tmap_1(A_772, '#skF_3', '#skF_5', D_773, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_773)) | ~m1_pre_topc(D_773, '#skF_5') | ~m1_pre_topc(D_773, A_772) | ~m1_pre_topc('#skF_5', A_772) | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772) | v2_struct_0(A_772))), inference(negUnitSimplification, [status(thm)], [c_72, c_728])).
% 4.68/1.91  tff(c_738, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_730])).
% 4.68/1.91  tff(c_750, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_52, c_738])).
% 4.68/1.91  tff(c_751, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_750])).
% 4.68/1.91  tff(c_647, plain, (![A_740, B_741, C_742, D_743]: (k2_partfun1(u1_struct_0(A_740), u1_struct_0(B_741), C_742, u1_struct_0(D_743))=k2_tmap_1(A_740, B_741, C_742, D_743) | ~m1_pre_topc(D_743, A_740) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_740), u1_struct_0(B_741)))) | ~v1_funct_2(C_742, u1_struct_0(A_740), u1_struct_0(B_741)) | ~v1_funct_1(C_742) | ~l1_pre_topc(B_741) | ~v2_pre_topc(B_741) | v2_struct_0(B_741) | ~l1_pre_topc(A_740) | ~v2_pre_topc(A_740) | v2_struct_0(A_740))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.68/1.91  tff(c_649, plain, (![D_743]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_743))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_743) | ~m1_pre_topc(D_743, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_647])).
% 4.68/1.91  tff(c_652, plain, (![D_743]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_743))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_743) | ~m1_pre_topc(D_743, '#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_109, c_70, c_68, c_58, c_56, c_649])).
% 4.68/1.91  tff(c_653, plain, (![D_743]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_743))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_743) | ~m1_pre_topc(D_743, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_72, c_652])).
% 4.68/1.91  tff(c_755, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_751, c_653])).
% 4.68/1.91  tff(c_762, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_755])).
% 4.68/1.91  tff(c_767, plain, (r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_178])).
% 4.68/1.91  tff(c_812, plain, (![E_799, D_798, A_802, C_796, B_800, F_797, H_801]: (r1_tmap_1(D_798, B_800, E_799, H_801) | ~r1_tmap_1(C_796, B_800, k3_tmap_1(A_802, B_800, D_798, C_796, E_799), H_801) | ~m1_connsp_2(F_797, D_798, H_801) | ~r1_tarski(F_797, u1_struct_0(C_796)) | ~m1_subset_1(H_801, u1_struct_0(C_796)) | ~m1_subset_1(H_801, u1_struct_0(D_798)) | ~m1_subset_1(F_797, k1_zfmisc_1(u1_struct_0(D_798))) | ~m1_pre_topc(C_796, D_798) | ~m1_subset_1(E_799, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_798), u1_struct_0(B_800)))) | ~v1_funct_2(E_799, u1_struct_0(D_798), u1_struct_0(B_800)) | ~v1_funct_1(E_799) | ~m1_pre_topc(D_798, A_802) | v2_struct_0(D_798) | ~m1_pre_topc(C_796, A_802) | v2_struct_0(C_796) | ~l1_pre_topc(B_800) | ~v2_pre_topc(B_800) | v2_struct_0(B_800) | ~l1_pre_topc(A_802) | ~v2_pre_topc(A_802) | v2_struct_0(A_802))), inference(cnfTransformation, [status(thm)], [f_267])).
% 4.68/1.91  tff(c_814, plain, (![H_801, F_797]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', H_801) | ~r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), H_801) | ~m1_connsp_2(F_797, '#skF_5', H_801) | ~r1_tarski(F_797, u1_struct_0('#skF_4')) | ~m1_subset_1(H_801, u1_struct_0('#skF_4')) | ~m1_subset_1(H_801, u1_struct_0('#skF_5')) | ~m1_subset_1(F_797, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_762, c_812])).
% 4.68/1.91  tff(c_816, plain, (![H_801, F_797]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', H_801) | ~r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), H_801) | ~m1_connsp_2(F_797, '#skF_5', H_801) | ~r1_tarski(F_797, u1_struct_0('#skF_4')) | ~m1_subset_1(H_801, u1_struct_0('#skF_4')) | ~m1_subset_1(H_801, u1_struct_0('#skF_5')) | ~m1_subset_1(F_797, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_56, c_54, c_52, c_814])).
% 4.68/1.91  tff(c_818, plain, (![H_803, F_804]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', H_803) | ~r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), H_803) | ~m1_connsp_2(F_804, '#skF_5', H_803) | ~r1_tarski(F_804, u1_struct_0('#skF_4')) | ~m1_subset_1(H_803, u1_struct_0('#skF_4')) | ~m1_subset_1(H_803, u1_struct_0('#skF_5')) | ~m1_subset_1(F_804, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_816])).
% 4.68/1.91  tff(c_823, plain, (![F_804]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_804, '#skF_5', '#skF_8') | ~r1_tarski(F_804, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_804, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_767, c_818])).
% 4.68/1.91  tff(c_830, plain, (![F_804]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_804, '#skF_5', '#skF_8') | ~r1_tarski(F_804, u1_struct_0('#skF_4')) | ~m1_subset_1(F_804, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_89, c_823])).
% 4.68/1.91  tff(c_832, plain, (![F_805]: (~m1_connsp_2(F_805, '#skF_5', '#skF_8') | ~r1_tarski(F_805, u1_struct_0('#skF_4')) | ~m1_subset_1(F_805, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_213, c_830])).
% 4.68/1.91  tff(c_835, plain, (~m1_connsp_2('#skF_7', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_832])).
% 4.68/1.91  tff(c_839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_447, c_835])).
% 4.68/1.91  tff(c_840, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 4.68/1.91  tff(c_1453, plain, (![F_914, A_915, D_918, B_917, C_916]: (r1_tmap_1(D_918, A_915, k2_tmap_1(B_917, A_915, C_916, D_918), F_914) | ~r1_tmap_1(B_917, A_915, C_916, F_914) | ~m1_subset_1(F_914, u1_struct_0(D_918)) | ~m1_subset_1(F_914, u1_struct_0(B_917)) | ~m1_pre_topc(D_918, B_917) | v2_struct_0(D_918) | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_917), u1_struct_0(A_915)))) | ~v1_funct_2(C_916, u1_struct_0(B_917), u1_struct_0(A_915)) | ~v1_funct_1(C_916) | ~l1_pre_topc(B_917) | ~v2_pre_topc(B_917) | v2_struct_0(B_917) | ~l1_pre_topc(A_915) | ~v2_pre_topc(A_915) | v2_struct_0(A_915))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.68/1.91  tff(c_1455, plain, (![D_918, F_914]: (r1_tmap_1(D_918, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_918), F_914) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_914) | ~m1_subset_1(F_914, u1_struct_0(D_918)) | ~m1_subset_1(F_914, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_918, '#skF_5') | v2_struct_0(D_918) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1453])).
% 4.68/1.91  tff(c_1458, plain, (![D_918, F_914]: (r1_tmap_1(D_918, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_918), F_914) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_914) | ~m1_subset_1(F_914, u1_struct_0(D_918)) | ~m1_subset_1(F_914, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_918, '#skF_5') | v2_struct_0(D_918) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_149, c_109, c_58, c_56, c_1455])).
% 4.68/1.91  tff(c_1460, plain, (![D_919, F_920]: (r1_tmap_1(D_919, '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_919), F_920) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', F_920) | ~m1_subset_1(F_920, u1_struct_0(D_919)) | ~m1_subset_1(F_920, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_919, '#skF_5') | v2_struct_0(D_919))), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_1458])).
% 4.68/1.91  tff(c_1386, plain, (![A_903, B_907, C_906, E_904, D_905]: (k3_tmap_1(A_903, B_907, C_906, D_905, E_904)=k2_partfun1(u1_struct_0(C_906), u1_struct_0(B_907), E_904, u1_struct_0(D_905)) | ~m1_pre_topc(D_905, C_906) | ~m1_subset_1(E_904, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_906), u1_struct_0(B_907)))) | ~v1_funct_2(E_904, u1_struct_0(C_906), u1_struct_0(B_907)) | ~v1_funct_1(E_904) | ~m1_pre_topc(D_905, A_903) | ~m1_pre_topc(C_906, A_903) | ~l1_pre_topc(B_907) | ~v2_pre_topc(B_907) | v2_struct_0(B_907) | ~l1_pre_topc(A_903) | ~v2_pre_topc(A_903) | v2_struct_0(A_903))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.68/1.91  tff(c_1388, plain, (![A_903, D_905]: (k3_tmap_1(A_903, '#skF_3', '#skF_5', D_905, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_905)) | ~m1_pre_topc(D_905, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_905, A_903) | ~m1_pre_topc('#skF_5', A_903) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_903) | ~v2_pre_topc(A_903) | v2_struct_0(A_903))), inference(resolution, [status(thm)], [c_54, c_1386])).
% 4.68/1.91  tff(c_1391, plain, (![A_903, D_905]: (k3_tmap_1(A_903, '#skF_3', '#skF_5', D_905, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_905)) | ~m1_pre_topc(D_905, '#skF_5') | ~m1_pre_topc(D_905, A_903) | ~m1_pre_topc('#skF_5', A_903) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_903) | ~v2_pre_topc(A_903) | v2_struct_0(A_903))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_56, c_1388])).
% 4.68/1.91  tff(c_1393, plain, (![A_908, D_909]: (k3_tmap_1(A_908, '#skF_3', '#skF_5', D_909, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_909)) | ~m1_pre_topc(D_909, '#skF_5') | ~m1_pre_topc(D_909, A_908) | ~m1_pre_topc('#skF_5', A_908) | ~l1_pre_topc(A_908) | ~v2_pre_topc(A_908) | v2_struct_0(A_908))), inference(negUnitSimplification, [status(thm)], [c_72, c_1391])).
% 4.68/1.91  tff(c_1401, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1393])).
% 4.68/1.91  tff(c_1413, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_52, c_1401])).
% 4.68/1.91  tff(c_1414, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_1413])).
% 4.68/1.91  tff(c_1310, plain, (![A_876, B_877, C_878, D_879]: (k2_partfun1(u1_struct_0(A_876), u1_struct_0(B_877), C_878, u1_struct_0(D_879))=k2_tmap_1(A_876, B_877, C_878, D_879) | ~m1_pre_topc(D_879, A_876) | ~m1_subset_1(C_878, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_876), u1_struct_0(B_877)))) | ~v1_funct_2(C_878, u1_struct_0(A_876), u1_struct_0(B_877)) | ~v1_funct_1(C_878) | ~l1_pre_topc(B_877) | ~v2_pre_topc(B_877) | v2_struct_0(B_877) | ~l1_pre_topc(A_876) | ~v2_pre_topc(A_876) | v2_struct_0(A_876))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.68/1.91  tff(c_1312, plain, (![D_879]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_879))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_879) | ~m1_pre_topc(D_879, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1310])).
% 4.68/1.91  tff(c_1315, plain, (![D_879]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_879))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_879) | ~m1_pre_topc(D_879, '#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_109, c_70, c_68, c_58, c_56, c_1312])).
% 4.68/1.91  tff(c_1316, plain, (![D_879]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_879))=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', D_879) | ~m1_pre_topc(D_879, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_72, c_1315])).
% 4.68/1.91  tff(c_1418, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1414, c_1316])).
% 4.68/1.91  tff(c_1425, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1418])).
% 4.68/1.91  tff(c_841, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 4.68/1.91  tff(c_1430, plain, (~r1_tmap_1('#skF_4', '#skF_3', k2_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_841])).
% 4.68/1.91  tff(c_1463, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1460, c_1430])).
% 4.68/1.91  tff(c_1466, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_89, c_840, c_1463])).
% 4.68/1.91  tff(c_1468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1466])).
% 4.68/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  Inference rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Ref     : 0
% 4.68/1.91  #Sup     : 282
% 4.68/1.91  #Fact    : 0
% 4.68/1.91  #Define  : 0
% 4.68/1.91  #Split   : 10
% 4.68/1.91  #Chain   : 0
% 4.68/1.91  #Close   : 0
% 4.68/1.91  
% 4.68/1.91  Ordering : KBO
% 4.68/1.91  
% 4.68/1.91  Simplification rules
% 4.68/1.91  ----------------------
% 4.68/1.91  #Subsume      : 107
% 4.68/1.91  #Demod        : 281
% 4.68/1.91  #Tautology    : 64
% 4.68/1.91  #SimpNegUnit  : 60
% 4.68/1.91  #BackRed      : 4
% 4.68/1.91  
% 4.68/1.91  #Partial instantiations: 0
% 4.68/1.91  #Strategies tried      : 1
% 4.68/1.91  
% 4.68/1.91  Timing (in seconds)
% 4.68/1.91  ----------------------
% 4.68/1.92  Preprocessing        : 0.42
% 4.68/1.92  Parsing              : 0.21
% 4.68/1.92  CNF conversion       : 0.06
% 4.68/1.92  Main loop            : 0.64
% 4.68/1.92  Inferencing          : 0.22
% 4.68/1.92  Reduction            : 0.22
% 4.68/1.92  Demodulation         : 0.15
% 4.68/1.92  BG Simplification    : 0.03
% 4.68/1.92  Subsumption          : 0.14
% 4.68/1.92  Abstraction          : 0.02
% 4.68/1.92  MUC search           : 0.00
% 5.04/1.92  Cooper               : 0.00
% 5.04/1.92  Total                : 1.12
% 5.04/1.92  Index Insertion      : 0.00
% 5.04/1.92  Index Deletion       : 0.00
% 5.04/1.92  Index Matching       : 0.00
% 5.04/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
