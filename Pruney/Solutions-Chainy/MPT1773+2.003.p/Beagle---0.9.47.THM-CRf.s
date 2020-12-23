%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:22 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 495 expanded)
%              Number of leaves         :   42 ( 207 expanded)
%              Depth                    :   17
%              Number of atoms          :  538 (4290 expanded)
%              Number of equality atoms :   36 ( 210 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_34,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_36,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_93,plain,(
    ! [B_652,A_653] :
      ( l1_pre_topc(B_652)
      | ~ m1_pre_topc(B_652,A_653)
      | ~ l1_pre_topc(A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_93])).

tff(c_109,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_102])).

tff(c_38,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_86,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_277,plain,(
    ! [C_680,A_681,B_682] :
      ( m1_subset_1(C_680,u1_struct_0(A_681))
      | ~ m1_subset_1(C_680,u1_struct_0(B_682))
      | ~ m1_pre_topc(B_682,A_681)
      | v2_struct_0(B_682)
      | ~ l1_pre_topc(A_681)
      | v2_struct_0(A_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_279,plain,(
    ! [A_681] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_681))
      | ~ m1_pre_topc('#skF_3',A_681)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_681)
      | v2_struct_0(A_681) ) ),
    inference(resolution,[status(thm)],[c_42,c_277])).

tff(c_284,plain,(
    ! [A_681] :
      ( m1_subset_1('#skF_8',u1_struct_0(A_681))
      | ~ m1_pre_topc('#skF_3',A_681)
      | ~ l1_pre_topc(A_681)
      | v2_struct_0(A_681) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_279])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_124,plain,(
    ! [B_656,A_657] :
      ( v2_pre_topc(B_656)
      | ~ m1_pre_topc(B_656,A_657)
      | ~ l1_pre_topc(A_657)
      | ~ v2_pre_topc(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_142,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_133])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_145,plain,(
    ! [A_658,B_659] :
      ( r1_tarski(k1_tops_1(A_658,B_659),B_659)
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ l1_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_147,plain,
    ( r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_150,plain,(
    r1_tarski(k1_tops_1('#skF_4','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_147])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,
    ( k1_tops_1('#skF_4','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_40,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [B_669,A_670,C_671] :
      ( r1_tarski(B_669,k1_tops_1(A_670,C_671))
      | ~ r1_tarski(B_669,C_671)
      | ~ v3_pre_topc(B_669,A_670)
      | ~ m1_subset_1(C_671,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ m1_subset_1(B_669,k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ l1_pre_topc(A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_208,plain,(
    ! [B_669] :
      ( r1_tarski(B_669,k1_tops_1('#skF_4','#skF_6'))
      | ~ r1_tarski(B_669,'#skF_6')
      | ~ v3_pre_topc(B_669,'#skF_4')
      | ~ m1_subset_1(B_669,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_220,plain,(
    ! [B_674] :
      ( r1_tarski(B_674,k1_tops_1('#skF_4','#skF_6'))
      | ~ r1_tarski(B_674,'#skF_6')
      | ~ v3_pre_topc(B_674,'#skF_4')
      | ~ m1_subset_1(B_674,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_208])).

tff(c_223,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_220])).

tff(c_226,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_223])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_226])).

tff(c_229,plain,(
    k1_tops_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_467,plain,(
    ! [C_703,A_704,B_705] :
      ( m1_connsp_2(C_703,A_704,B_705)
      | ~ r2_hidden(B_705,k1_tops_1(A_704,C_703))
      | ~ m1_subset_1(C_703,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_subset_1(B_705,u1_struct_0(A_704))
      | ~ l1_pre_topc(A_704)
      | ~ v2_pre_topc(A_704)
      | v2_struct_0(A_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_469,plain,(
    ! [B_705] :
      ( m1_connsp_2('#skF_6','#skF_4',B_705)
      | ~ r2_hidden(B_705,'#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_467])).

tff(c_471,plain,(
    ! [B_705] :
      ( m1_connsp_2('#skF_6','#skF_4',B_705)
      | ~ r2_hidden(B_705,'#skF_6')
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_109,c_46,c_469])).

tff(c_503,plain,(
    ! [B_707] :
      ( m1_connsp_2('#skF_6','#skF_4',B_707)
      | ~ r2_hidden(B_707,'#skF_6')
      | ~ m1_subset_1(B_707,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_471])).

tff(c_515,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_284,c_503])).

tff(c_529,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_48,c_86,c_515])).

tff(c_530,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_529])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_123,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_552,plain,(
    ! [D_717,C_715,A_713,B_714,E_716] :
      ( k3_tmap_1(A_713,B_714,C_715,D_717,E_716) = k2_partfun1(u1_struct_0(C_715),u1_struct_0(B_714),E_716,u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,C_715)
      | ~ m1_subset_1(E_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715),u1_struct_0(B_714))))
      | ~ v1_funct_2(E_716,u1_struct_0(C_715),u1_struct_0(B_714))
      | ~ v1_funct_1(E_716)
      | ~ m1_pre_topc(D_717,A_713)
      | ~ m1_pre_topc(C_715,A_713)
      | ~ l1_pre_topc(B_714)
      | ~ v2_pre_topc(B_714)
      | v2_struct_0(B_714)
      | ~ l1_pre_topc(A_713)
      | ~ v2_pre_topc(A_713)
      | v2_struct_0(A_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_554,plain,(
    ! [A_713,D_717] :
      ( k3_tmap_1(A_713,'#skF_2','#skF_4',D_717,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_717,A_713)
      | ~ m1_pre_topc('#skF_4',A_713)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_713)
      | ~ v2_pre_topc(A_713)
      | v2_struct_0(A_713) ) ),
    inference(resolution,[status(thm)],[c_50,c_552])).

tff(c_557,plain,(
    ! [A_713,D_717] :
      ( k3_tmap_1(A_713,'#skF_2','#skF_4',D_717,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_717))
      | ~ m1_pre_topc(D_717,'#skF_4')
      | ~ m1_pre_topc(D_717,A_713)
      | ~ m1_pre_topc('#skF_4',A_713)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_713)
      | ~ v2_pre_topc(A_713)
      | v2_struct_0(A_713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_554])).

tff(c_559,plain,(
    ! [A_718,D_719] :
      ( k3_tmap_1(A_718,'#skF_2','#skF_4',D_719,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_719))
      | ~ m1_pre_topc(D_719,'#skF_4')
      | ~ m1_pre_topc(D_719,A_718)
      | ~ m1_pre_topc('#skF_4',A_718)
      | ~ l1_pre_topc(A_718)
      | ~ v2_pre_topc(A_718)
      | v2_struct_0(A_718) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_557])).

tff(c_565,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_559])).

tff(c_578,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_48,c_565])).

tff(c_579,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_578])).

tff(c_536,plain,(
    ! [A_708,B_709,C_710,D_711] :
      ( k2_partfun1(u1_struct_0(A_708),u1_struct_0(B_709),C_710,u1_struct_0(D_711)) = k2_tmap_1(A_708,B_709,C_710,D_711)
      | ~ m1_pre_topc(D_711,A_708)
      | ~ m1_subset_1(C_710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_708),u1_struct_0(B_709))))
      | ~ v1_funct_2(C_710,u1_struct_0(A_708),u1_struct_0(B_709))
      | ~ v1_funct_1(C_710)
      | ~ l1_pre_topc(B_709)
      | ~ v2_pre_topc(B_709)
      | v2_struct_0(B_709)
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_538,plain,(
    ! [D_711] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_711)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_711)
      | ~ m1_pre_topc(D_711,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_536])).

tff(c_541,plain,(
    ! [D_711] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_711)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_711)
      | ~ m1_pre_topc(D_711,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_109,c_66,c_64,c_54,c_52,c_538])).

tff(c_542,plain,(
    ! [D_711] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_711)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_711)
      | ~ m1_pre_topc(D_711,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_541])).

tff(c_598,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_542])).

tff(c_605,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_598])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_231,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_83])).

tff(c_610,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_231])).

tff(c_643,plain,(
    ! [A_730,B_728,E_729,C_733,F_731,H_734,D_732] :
      ( r1_tmap_1(D_732,B_728,E_729,H_734)
      | ~ r1_tmap_1(C_733,B_728,k3_tmap_1(A_730,B_728,D_732,C_733,E_729),H_734)
      | ~ m1_connsp_2(F_731,D_732,H_734)
      | ~ r1_tarski(F_731,u1_struct_0(C_733))
      | ~ m1_subset_1(H_734,u1_struct_0(C_733))
      | ~ m1_subset_1(H_734,u1_struct_0(D_732))
      | ~ m1_subset_1(F_731,k1_zfmisc_1(u1_struct_0(D_732)))
      | ~ m1_pre_topc(C_733,D_732)
      | ~ m1_subset_1(E_729,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_732),u1_struct_0(B_728))))
      | ~ v1_funct_2(E_729,u1_struct_0(D_732),u1_struct_0(B_728))
      | ~ v1_funct_1(E_729)
      | ~ m1_pre_topc(D_732,A_730)
      | v2_struct_0(D_732)
      | ~ m1_pre_topc(C_733,A_730)
      | v2_struct_0(C_733)
      | ~ l1_pre_topc(B_728)
      | ~ v2_pre_topc(B_728)
      | v2_struct_0(B_728)
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_645,plain,(
    ! [H_734,F_731] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',H_734)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),H_734)
      | ~ m1_connsp_2(F_731,'#skF_4',H_734)
      | ~ r1_tarski(F_731,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_734,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_734,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_731,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_643])).

tff(c_647,plain,(
    ! [H_734,F_731] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',H_734)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),H_734)
      | ~ m1_connsp_2(F_731,'#skF_4',H_734)
      | ~ r1_tarski(F_731,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_734,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_734,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_731,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_48,c_645])).

tff(c_656,plain,(
    ! [H_742,F_743] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',H_742)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),H_742)
      | ~ m1_connsp_2(F_743,'#skF_4',H_742)
      | ~ r1_tarski(F_743,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_742,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_742,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_743,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_647])).

tff(c_661,plain,(
    ! [F_743] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_743,'#skF_4','#skF_8')
      | ~ r1_tarski(F_743,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_743,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_610,c_656])).

tff(c_668,plain,(
    ! [F_743] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_743,'#skF_4','#skF_8')
      | ~ r1_tarski(F_743,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_743,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_42,c_661])).

tff(c_670,plain,(
    ! [F_744] :
      ( ~ m1_connsp_2(F_744,'#skF_4','#skF_8')
      | ~ r1_tarski(F_744,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_744,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_668])).

tff(c_673,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_670])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_530,c_673])).

tff(c_679,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_681,plain,(
    ! [B_745,A_746] :
      ( v2_pre_topc(B_745)
      | ~ m1_pre_topc(B_745,A_746)
      | ~ l1_pre_topc(A_746)
      | ~ v2_pre_topc(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_690,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_681])).

tff(c_699,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_690])).

tff(c_1182,plain,(
    ! [D_812,C_809,F_810,B_813,A_811] :
      ( r1_tmap_1(D_812,A_811,k2_tmap_1(B_813,A_811,C_809,D_812),F_810)
      | ~ r1_tmap_1(B_813,A_811,C_809,F_810)
      | ~ m1_subset_1(F_810,u1_struct_0(D_812))
      | ~ m1_subset_1(F_810,u1_struct_0(B_813))
      | ~ m1_pre_topc(D_812,B_813)
      | v2_struct_0(D_812)
      | ~ m1_subset_1(C_809,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_813),u1_struct_0(A_811))))
      | ~ v1_funct_2(C_809,u1_struct_0(B_813),u1_struct_0(A_811))
      | ~ v1_funct_1(C_809)
      | ~ l1_pre_topc(B_813)
      | ~ v2_pre_topc(B_813)
      | v2_struct_0(B_813)
      | ~ l1_pre_topc(A_811)
      | ~ v2_pre_topc(A_811)
      | v2_struct_0(A_811) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1184,plain,(
    ! [D_812,F_810] :
      ( r1_tmap_1(D_812,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_812),F_810)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_810)
      | ~ m1_subset_1(F_810,u1_struct_0(D_812))
      | ~ m1_subset_1(F_810,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_812,'#skF_4')
      | v2_struct_0(D_812)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1182])).

tff(c_1187,plain,(
    ! [D_812,F_810] :
      ( r1_tmap_1(D_812,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_812),F_810)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_810)
      | ~ m1_subset_1(F_810,u1_struct_0(D_812))
      | ~ m1_subset_1(F_810,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_812,'#skF_4')
      | v2_struct_0(D_812)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_699,c_109,c_54,c_52,c_1184])).

tff(c_1198,plain,(
    ! [D_815,F_816] :
      ( r1_tmap_1(D_815,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_815),F_816)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',F_816)
      | ~ m1_subset_1(F_816,u1_struct_0(D_815))
      | ~ m1_subset_1(F_816,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_815,'#skF_4')
      | v2_struct_0(D_815) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_1187])).

tff(c_1107,plain,(
    ! [A_802,E_805,D_806,B_803,C_804] :
      ( k3_tmap_1(A_802,B_803,C_804,D_806,E_805) = k2_partfun1(u1_struct_0(C_804),u1_struct_0(B_803),E_805,u1_struct_0(D_806))
      | ~ m1_pre_topc(D_806,C_804)
      | ~ m1_subset_1(E_805,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_804),u1_struct_0(B_803))))
      | ~ v1_funct_2(E_805,u1_struct_0(C_804),u1_struct_0(B_803))
      | ~ v1_funct_1(E_805)
      | ~ m1_pre_topc(D_806,A_802)
      | ~ m1_pre_topc(C_804,A_802)
      | ~ l1_pre_topc(B_803)
      | ~ v2_pre_topc(B_803)
      | v2_struct_0(B_803)
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1109,plain,(
    ! [A_802,D_806] :
      ( k3_tmap_1(A_802,'#skF_2','#skF_4',D_806,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_806))
      | ~ m1_pre_topc(D_806,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_806,A_802)
      | ~ m1_pre_topc('#skF_4',A_802)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(resolution,[status(thm)],[c_50,c_1107])).

tff(c_1112,plain,(
    ! [A_802,D_806] :
      ( k3_tmap_1(A_802,'#skF_2','#skF_4',D_806,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_806))
      | ~ m1_pre_topc(D_806,'#skF_4')
      | ~ m1_pre_topc(D_806,A_802)
      | ~ m1_pre_topc('#skF_4',A_802)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_802)
      | ~ v2_pre_topc(A_802)
      | v2_struct_0(A_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_1109])).

tff(c_1114,plain,(
    ! [A_807,D_808] :
      ( k3_tmap_1(A_807,'#skF_2','#skF_4',D_808,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_808))
      | ~ m1_pre_topc(D_808,'#skF_4')
      | ~ m1_pre_topc(D_808,A_807)
      | ~ m1_pre_topc('#skF_4',A_807)
      | ~ l1_pre_topc(A_807)
      | ~ v2_pre_topc(A_807)
      | v2_struct_0(A_807) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1112])).

tff(c_1120,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1114])).

tff(c_1133,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_48,c_1120])).

tff(c_1134,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1133])).

tff(c_1091,plain,(
    ! [A_797,B_798,C_799,D_800] :
      ( k2_partfun1(u1_struct_0(A_797),u1_struct_0(B_798),C_799,u1_struct_0(D_800)) = k2_tmap_1(A_797,B_798,C_799,D_800)
      | ~ m1_pre_topc(D_800,A_797)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_797),u1_struct_0(B_798))))
      | ~ v1_funct_2(C_799,u1_struct_0(A_797),u1_struct_0(B_798))
      | ~ v1_funct_1(C_799)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_797)
      | ~ v2_pre_topc(A_797)
      | v2_struct_0(A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1093,plain,(
    ! [D_800] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_800)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_800)
      | ~ m1_pre_topc(D_800,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_1091])).

tff(c_1096,plain,(
    ! [D_800] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_800)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_800)
      | ~ m1_pre_topc(D_800,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_109,c_66,c_64,c_54,c_52,c_1093])).

tff(c_1097,plain,(
    ! [D_800] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_800)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_800)
      | ~ m1_pre_topc(D_800,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_1096])).

tff(c_1146,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_1097])).

tff(c_1153,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1146])).

tff(c_678,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1158,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_678])).

tff(c_1201,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1198,c_1158])).

tff(c_1204,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_85,c_42,c_679,c_1201])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.73  
% 4.39/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.73  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.39/1.73  
% 4.39/1.73  %Foreground sorts:
% 4.39/1.73  
% 4.39/1.73  
% 4.39/1.73  %Background operators:
% 4.39/1.73  
% 4.39/1.73  
% 4.39/1.73  %Foreground operators:
% 4.39/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.39/1.73  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.39/1.73  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.39/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.39/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.39/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.73  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.39/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.39/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.39/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.39/1.73  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.39/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.39/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.39/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.39/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.39/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.39/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.39/1.73  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.39/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.39/1.73  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.39/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.39/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.73  
% 4.72/1.76  tff(f_325, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.72/1.76  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.72/1.76  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 4.72/1.76  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.72/1.76  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.72/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.72/1.76  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.72/1.76  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.72/1.76  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.72/1.76  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.72/1.76  tff(f_267, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.72/1.76  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.72/1.76  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_34, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 4.72/1.76  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_36, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_93, plain, (![B_652, A_653]: (l1_pre_topc(B_652) | ~m1_pre_topc(B_652, A_653) | ~l1_pre_topc(A_653))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.72/1.76  tff(c_102, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_93])).
% 4.72/1.76  tff(c_109, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_102])).
% 4.72/1.76  tff(c_38, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_86, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 4.72/1.76  tff(c_277, plain, (![C_680, A_681, B_682]: (m1_subset_1(C_680, u1_struct_0(A_681)) | ~m1_subset_1(C_680, u1_struct_0(B_682)) | ~m1_pre_topc(B_682, A_681) | v2_struct_0(B_682) | ~l1_pre_topc(A_681) | v2_struct_0(A_681))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.76  tff(c_279, plain, (![A_681]: (m1_subset_1('#skF_8', u1_struct_0(A_681)) | ~m1_pre_topc('#skF_3', A_681) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_681) | v2_struct_0(A_681))), inference(resolution, [status(thm)], [c_42, c_277])).
% 4.72/1.76  tff(c_284, plain, (![A_681]: (m1_subset_1('#skF_8', u1_struct_0(A_681)) | ~m1_pre_topc('#skF_3', A_681) | ~l1_pre_topc(A_681) | v2_struct_0(A_681))), inference(negUnitSimplification, [status(thm)], [c_62, c_279])).
% 4.72/1.76  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_124, plain, (![B_656, A_657]: (v2_pre_topc(B_656) | ~m1_pre_topc(B_656, A_657) | ~l1_pre_topc(A_657) | ~v2_pre_topc(A_657))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.72/1.76  tff(c_133, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_124])).
% 4.72/1.76  tff(c_142, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_133])).
% 4.72/1.76  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_145, plain, (![A_658, B_659]: (r1_tarski(k1_tops_1(A_658, B_659), B_659) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0(A_658))) | ~l1_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.72/1.76  tff(c_147, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_145])).
% 4.72/1.76  tff(c_150, plain, (r1_tarski(k1_tops_1('#skF_4', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_147])).
% 4.72/1.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.76  tff(c_153, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_150, c_2])).
% 4.72/1.76  tff(c_154, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_153])).
% 4.72/1.76  tff(c_40, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.72/1.76  tff(c_206, plain, (![B_669, A_670, C_671]: (r1_tarski(B_669, k1_tops_1(A_670, C_671)) | ~r1_tarski(B_669, C_671) | ~v3_pre_topc(B_669, A_670) | ~m1_subset_1(C_671, k1_zfmisc_1(u1_struct_0(A_670))) | ~m1_subset_1(B_669, k1_zfmisc_1(u1_struct_0(A_670))) | ~l1_pre_topc(A_670))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.72/1.76  tff(c_208, plain, (![B_669]: (r1_tarski(B_669, k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski(B_669, '#skF_6') | ~v3_pre_topc(B_669, '#skF_4') | ~m1_subset_1(B_669, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_206])).
% 4.72/1.76  tff(c_220, plain, (![B_674]: (r1_tarski(B_674, k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski(B_674, '#skF_6') | ~v3_pre_topc(B_674, '#skF_4') | ~m1_subset_1(B_674, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_208])).
% 4.72/1.76  tff(c_223, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_220])).
% 4.72/1.76  tff(c_226, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_223])).
% 4.72/1.76  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_226])).
% 4.72/1.76  tff(c_229, plain, (k1_tops_1('#skF_4', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_153])).
% 4.72/1.76  tff(c_467, plain, (![C_703, A_704, B_705]: (m1_connsp_2(C_703, A_704, B_705) | ~r2_hidden(B_705, k1_tops_1(A_704, C_703)) | ~m1_subset_1(C_703, k1_zfmisc_1(u1_struct_0(A_704))) | ~m1_subset_1(B_705, u1_struct_0(A_704)) | ~l1_pre_topc(A_704) | ~v2_pre_topc(A_704) | v2_struct_0(A_704))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.72/1.76  tff(c_469, plain, (![B_705]: (m1_connsp_2('#skF_6', '#skF_4', B_705) | ~r2_hidden(B_705, '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_705, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_467])).
% 4.72/1.76  tff(c_471, plain, (![B_705]: (m1_connsp_2('#skF_6', '#skF_4', B_705) | ~r2_hidden(B_705, '#skF_6') | ~m1_subset_1(B_705, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_109, c_46, c_469])).
% 4.72/1.76  tff(c_503, plain, (![B_707]: (m1_connsp_2('#skF_6', '#skF_4', B_707) | ~r2_hidden(B_707, '#skF_6') | ~m1_subset_1(B_707, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_471])).
% 4.72/1.76  tff(c_515, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_284, c_503])).
% 4.72/1.76  tff(c_529, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_48, c_86, c_515])).
% 4.72/1.76  tff(c_530, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_58, c_529])).
% 4.72/1.76  tff(c_76, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_84, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 4.72/1.76  tff(c_123, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 4.72/1.76  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_552, plain, (![D_717, C_715, A_713, B_714, E_716]: (k3_tmap_1(A_713, B_714, C_715, D_717, E_716)=k2_partfun1(u1_struct_0(C_715), u1_struct_0(B_714), E_716, u1_struct_0(D_717)) | ~m1_pre_topc(D_717, C_715) | ~m1_subset_1(E_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715), u1_struct_0(B_714)))) | ~v1_funct_2(E_716, u1_struct_0(C_715), u1_struct_0(B_714)) | ~v1_funct_1(E_716) | ~m1_pre_topc(D_717, A_713) | ~m1_pre_topc(C_715, A_713) | ~l1_pre_topc(B_714) | ~v2_pre_topc(B_714) | v2_struct_0(B_714) | ~l1_pre_topc(A_713) | ~v2_pre_topc(A_713) | v2_struct_0(A_713))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.76  tff(c_554, plain, (![A_713, D_717]: (k3_tmap_1(A_713, '#skF_2', '#skF_4', D_717, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_717)) | ~m1_pre_topc(D_717, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_717, A_713) | ~m1_pre_topc('#skF_4', A_713) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_713) | ~v2_pre_topc(A_713) | v2_struct_0(A_713))), inference(resolution, [status(thm)], [c_50, c_552])).
% 4.72/1.76  tff(c_557, plain, (![A_713, D_717]: (k3_tmap_1(A_713, '#skF_2', '#skF_4', D_717, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_717)) | ~m1_pre_topc(D_717, '#skF_4') | ~m1_pre_topc(D_717, A_713) | ~m1_pre_topc('#skF_4', A_713) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_713) | ~v2_pre_topc(A_713) | v2_struct_0(A_713))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_554])).
% 4.72/1.76  tff(c_559, plain, (![A_718, D_719]: (k3_tmap_1(A_718, '#skF_2', '#skF_4', D_719, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_719)) | ~m1_pre_topc(D_719, '#skF_4') | ~m1_pre_topc(D_719, A_718) | ~m1_pre_topc('#skF_4', A_718) | ~l1_pre_topc(A_718) | ~v2_pre_topc(A_718) | v2_struct_0(A_718))), inference(negUnitSimplification, [status(thm)], [c_68, c_557])).
% 4.72/1.76  tff(c_565, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_559])).
% 4.72/1.76  tff(c_578, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_48, c_565])).
% 4.72/1.76  tff(c_579, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_578])).
% 4.72/1.76  tff(c_536, plain, (![A_708, B_709, C_710, D_711]: (k2_partfun1(u1_struct_0(A_708), u1_struct_0(B_709), C_710, u1_struct_0(D_711))=k2_tmap_1(A_708, B_709, C_710, D_711) | ~m1_pre_topc(D_711, A_708) | ~m1_subset_1(C_710, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_708), u1_struct_0(B_709)))) | ~v1_funct_2(C_710, u1_struct_0(A_708), u1_struct_0(B_709)) | ~v1_funct_1(C_710) | ~l1_pre_topc(B_709) | ~v2_pre_topc(B_709) | v2_struct_0(B_709) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.72/1.76  tff(c_538, plain, (![D_711]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_711))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_711) | ~m1_pre_topc(D_711, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_536])).
% 4.72/1.76  tff(c_541, plain, (![D_711]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_711))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_711) | ~m1_pre_topc(D_711, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_109, c_66, c_64, c_54, c_52, c_538])).
% 4.72/1.76  tff(c_542, plain, (![D_711]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_711))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_711) | ~m1_pre_topc(D_711, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_541])).
% 4.72/1.76  tff(c_598, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_579, c_542])).
% 4.72/1.76  tff(c_605, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_598])).
% 4.72/1.76  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_325])).
% 4.72/1.76  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_82])).
% 4.72/1.76  tff(c_231, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_123, c_83])).
% 4.72/1.76  tff(c_610, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_231])).
% 4.72/1.76  tff(c_643, plain, (![A_730, B_728, E_729, C_733, F_731, H_734, D_732]: (r1_tmap_1(D_732, B_728, E_729, H_734) | ~r1_tmap_1(C_733, B_728, k3_tmap_1(A_730, B_728, D_732, C_733, E_729), H_734) | ~m1_connsp_2(F_731, D_732, H_734) | ~r1_tarski(F_731, u1_struct_0(C_733)) | ~m1_subset_1(H_734, u1_struct_0(C_733)) | ~m1_subset_1(H_734, u1_struct_0(D_732)) | ~m1_subset_1(F_731, k1_zfmisc_1(u1_struct_0(D_732))) | ~m1_pre_topc(C_733, D_732) | ~m1_subset_1(E_729, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_732), u1_struct_0(B_728)))) | ~v1_funct_2(E_729, u1_struct_0(D_732), u1_struct_0(B_728)) | ~v1_funct_1(E_729) | ~m1_pre_topc(D_732, A_730) | v2_struct_0(D_732) | ~m1_pre_topc(C_733, A_730) | v2_struct_0(C_733) | ~l1_pre_topc(B_728) | ~v2_pre_topc(B_728) | v2_struct_0(B_728) | ~l1_pre_topc(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730))), inference(cnfTransformation, [status(thm)], [f_267])).
% 4.72/1.76  tff(c_645, plain, (![H_734, F_731]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_734) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), H_734) | ~m1_connsp_2(F_731, '#skF_4', H_734) | ~r1_tarski(F_731, u1_struct_0('#skF_3')) | ~m1_subset_1(H_734, u1_struct_0('#skF_3')) | ~m1_subset_1(H_734, u1_struct_0('#skF_4')) | ~m1_subset_1(F_731, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_605, c_643])).
% 4.72/1.76  tff(c_647, plain, (![H_734, F_731]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_734) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), H_734) | ~m1_connsp_2(F_731, '#skF_4', H_734) | ~r1_tarski(F_731, u1_struct_0('#skF_3')) | ~m1_subset_1(H_734, u1_struct_0('#skF_3')) | ~m1_subset_1(H_734, u1_struct_0('#skF_4')) | ~m1_subset_1(F_731, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_48, c_645])).
% 4.72/1.76  tff(c_656, plain, (![H_742, F_743]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_742) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), H_742) | ~m1_connsp_2(F_743, '#skF_4', H_742) | ~r1_tarski(F_743, u1_struct_0('#skF_3')) | ~m1_subset_1(H_742, u1_struct_0('#skF_3')) | ~m1_subset_1(H_742, u1_struct_0('#skF_4')) | ~m1_subset_1(F_743, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_647])).
% 4.72/1.76  tff(c_661, plain, (![F_743]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_743, '#skF_4', '#skF_8') | ~r1_tarski(F_743, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_743, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_610, c_656])).
% 4.72/1.76  tff(c_668, plain, (![F_743]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(F_743, '#skF_4', '#skF_8') | ~r1_tarski(F_743, u1_struct_0('#skF_3')) | ~m1_subset_1(F_743, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_42, c_661])).
% 4.72/1.76  tff(c_670, plain, (![F_744]: (~m1_connsp_2(F_744, '#skF_4', '#skF_8') | ~r1_tarski(F_744, u1_struct_0('#skF_3')) | ~m1_subset_1(F_744, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_123, c_668])).
% 4.72/1.76  tff(c_673, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_670])).
% 4.72/1.76  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_530, c_673])).
% 4.72/1.76  tff(c_679, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.72/1.76  tff(c_681, plain, (![B_745, A_746]: (v2_pre_topc(B_745) | ~m1_pre_topc(B_745, A_746) | ~l1_pre_topc(A_746) | ~v2_pre_topc(A_746))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.72/1.76  tff(c_690, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_681])).
% 4.72/1.76  tff(c_699, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_690])).
% 4.72/1.76  tff(c_1182, plain, (![D_812, C_809, F_810, B_813, A_811]: (r1_tmap_1(D_812, A_811, k2_tmap_1(B_813, A_811, C_809, D_812), F_810) | ~r1_tmap_1(B_813, A_811, C_809, F_810) | ~m1_subset_1(F_810, u1_struct_0(D_812)) | ~m1_subset_1(F_810, u1_struct_0(B_813)) | ~m1_pre_topc(D_812, B_813) | v2_struct_0(D_812) | ~m1_subset_1(C_809, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_813), u1_struct_0(A_811)))) | ~v1_funct_2(C_809, u1_struct_0(B_813), u1_struct_0(A_811)) | ~v1_funct_1(C_809) | ~l1_pre_topc(B_813) | ~v2_pre_topc(B_813) | v2_struct_0(B_813) | ~l1_pre_topc(A_811) | ~v2_pre_topc(A_811) | v2_struct_0(A_811))), inference(cnfTransformation, [status(thm)], [f_200])).
% 4.72/1.76  tff(c_1184, plain, (![D_812, F_810]: (r1_tmap_1(D_812, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_812), F_810) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_810) | ~m1_subset_1(F_810, u1_struct_0(D_812)) | ~m1_subset_1(F_810, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_812, '#skF_4') | v2_struct_0(D_812) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1182])).
% 4.72/1.76  tff(c_1187, plain, (![D_812, F_810]: (r1_tmap_1(D_812, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_812), F_810) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_810) | ~m1_subset_1(F_810, u1_struct_0(D_812)) | ~m1_subset_1(F_810, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_812, '#skF_4') | v2_struct_0(D_812) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_699, c_109, c_54, c_52, c_1184])).
% 4.72/1.76  tff(c_1198, plain, (![D_815, F_816]: (r1_tmap_1(D_815, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_815), F_816) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_816) | ~m1_subset_1(F_816, u1_struct_0(D_815)) | ~m1_subset_1(F_816, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_815, '#skF_4') | v2_struct_0(D_815))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_1187])).
% 4.72/1.76  tff(c_1107, plain, (![A_802, E_805, D_806, B_803, C_804]: (k3_tmap_1(A_802, B_803, C_804, D_806, E_805)=k2_partfun1(u1_struct_0(C_804), u1_struct_0(B_803), E_805, u1_struct_0(D_806)) | ~m1_pre_topc(D_806, C_804) | ~m1_subset_1(E_805, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_804), u1_struct_0(B_803)))) | ~v1_funct_2(E_805, u1_struct_0(C_804), u1_struct_0(B_803)) | ~v1_funct_1(E_805) | ~m1_pre_topc(D_806, A_802) | ~m1_pre_topc(C_804, A_802) | ~l1_pre_topc(B_803) | ~v2_pre_topc(B_803) | v2_struct_0(B_803) | ~l1_pre_topc(A_802) | ~v2_pre_topc(A_802) | v2_struct_0(A_802))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.72/1.76  tff(c_1109, plain, (![A_802, D_806]: (k3_tmap_1(A_802, '#skF_2', '#skF_4', D_806, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_806)) | ~m1_pre_topc(D_806, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_806, A_802) | ~m1_pre_topc('#skF_4', A_802) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_802) | ~v2_pre_topc(A_802) | v2_struct_0(A_802))), inference(resolution, [status(thm)], [c_50, c_1107])).
% 4.72/1.76  tff(c_1112, plain, (![A_802, D_806]: (k3_tmap_1(A_802, '#skF_2', '#skF_4', D_806, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_806)) | ~m1_pre_topc(D_806, '#skF_4') | ~m1_pre_topc(D_806, A_802) | ~m1_pre_topc('#skF_4', A_802) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_802) | ~v2_pre_topc(A_802) | v2_struct_0(A_802))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_1109])).
% 4.72/1.76  tff(c_1114, plain, (![A_807, D_808]: (k3_tmap_1(A_807, '#skF_2', '#skF_4', D_808, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_808)) | ~m1_pre_topc(D_808, '#skF_4') | ~m1_pre_topc(D_808, A_807) | ~m1_pre_topc('#skF_4', A_807) | ~l1_pre_topc(A_807) | ~v2_pre_topc(A_807) | v2_struct_0(A_807))), inference(negUnitSimplification, [status(thm)], [c_68, c_1112])).
% 4.72/1.76  tff(c_1120, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1114])).
% 4.72/1.76  tff(c_1133, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_48, c_1120])).
% 4.72/1.76  tff(c_1134, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_1133])).
% 4.72/1.76  tff(c_1091, plain, (![A_797, B_798, C_799, D_800]: (k2_partfun1(u1_struct_0(A_797), u1_struct_0(B_798), C_799, u1_struct_0(D_800))=k2_tmap_1(A_797, B_798, C_799, D_800) | ~m1_pre_topc(D_800, A_797) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_797), u1_struct_0(B_798)))) | ~v1_funct_2(C_799, u1_struct_0(A_797), u1_struct_0(B_798)) | ~v1_funct_1(C_799) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_797) | ~v2_pre_topc(A_797) | v2_struct_0(A_797))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.72/1.76  tff(c_1093, plain, (![D_800]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_800))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_800) | ~m1_pre_topc(D_800, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_1091])).
% 4.72/1.76  tff(c_1096, plain, (![D_800]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_800))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_800) | ~m1_pre_topc(D_800, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_109, c_66, c_64, c_54, c_52, c_1093])).
% 4.72/1.76  tff(c_1097, plain, (![D_800]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_800))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_800) | ~m1_pre_topc(D_800, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_1096])).
% 4.72/1.76  tff(c_1146, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1134, c_1097])).
% 4.72/1.76  tff(c_1153, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1146])).
% 4.72/1.76  tff(c_678, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.72/1.76  tff(c_1158, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_678])).
% 4.72/1.76  tff(c_1201, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1198, c_1158])).
% 4.72/1.76  tff(c_1204, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_85, c_42, c_679, c_1201])).
% 4.72/1.76  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1204])).
% 4.72/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.76  
% 4.72/1.76  Inference rules
% 4.72/1.76  ----------------------
% 4.72/1.76  #Ref     : 0
% 4.72/1.76  #Sup     : 201
% 4.72/1.76  #Fact    : 0
% 4.72/1.76  #Define  : 0
% 4.72/1.76  #Split   : 7
% 4.72/1.76  #Chain   : 0
% 4.72/1.76  #Close   : 0
% 4.72/1.76  
% 4.72/1.76  Ordering : KBO
% 4.72/1.76  
% 4.72/1.76  Simplification rules
% 4.72/1.76  ----------------------
% 4.72/1.76  #Subsume      : 26
% 4.72/1.76  #Demod        : 355
% 4.72/1.76  #Tautology    : 99
% 4.72/1.76  #SimpNegUnit  : 79
% 4.72/1.76  #BackRed      : 6
% 4.72/1.76  
% 4.72/1.76  #Partial instantiations: 0
% 4.72/1.76  #Strategies tried      : 1
% 4.72/1.76  
% 4.72/1.76  Timing (in seconds)
% 4.72/1.76  ----------------------
% 4.72/1.76  Preprocessing        : 0.46
% 4.72/1.76  Parsing              : 0.22
% 4.72/1.76  CNF conversion       : 0.08
% 4.72/1.76  Main loop            : 0.50
% 4.72/1.76  Inferencing          : 0.17
% 4.72/1.76  Reduction            : 0.18
% 4.72/1.76  Demodulation         : 0.13
% 4.72/1.76  BG Simplification    : 0.03
% 4.72/1.76  Subsumption          : 0.10
% 4.72/1.76  Abstraction          : 0.02
% 4.72/1.76  MUC search           : 0.00
% 4.72/1.76  Cooper               : 0.00
% 4.72/1.76  Total                : 1.03
% 4.72/1.76  Index Insertion      : 0.00
% 4.72/1.76  Index Deletion       : 0.00
% 4.72/1.76  Index Matching       : 0.00
% 4.72/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
