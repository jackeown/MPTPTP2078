%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 346 expanded)
%              Number of leaves         :   42 ( 149 expanded)
%              Depth                    :   19
%              Number of atoms          :  356 (2240 expanded)
%              Number of equality atoms :    6 ( 177 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_219,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ~ ( ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( r2_hidden(D,C)
                      <=> ( v3_pre_topc(D,A)
                          & v4_pre_topc(D,A)
                          & r2_hidden(B,D) ) ) )
                  & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_88,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_86,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_76,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_147,plain,(
    ! [B_423,A_424] :
      ( v2_pre_topc(B_423)
      | ~ m1_pre_topc(B_423,A_424)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_156,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_147])).

tff(c_163,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_156])).

tff(c_115,plain,(
    ! [B_417,A_418] :
      ( l1_pre_topc(B_417)
      | ~ m1_pre_topc(B_417,A_418)
      | ~ l1_pre_topc(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_115])).

tff(c_131,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_124])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_22,B_30] :
      ( r2_hidden('#skF_1'(A_22,B_30,k1_xboole_0),k1_xboole_0)
      | r2_hidden(B_30,'#skF_1'(A_22,B_30,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_407,plain,(
    ! [A_469,B_470] :
      ( r2_hidden('#skF_1'(A_469,B_470,k1_xboole_0),k1_xboole_0)
      | r2_hidden(B_470,'#skF_1'(A_469,B_470,k1_xboole_0))
      | ~ m1_subset_1(B_470,u1_struct_0(A_469))
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_416,plain,(
    ! [A_469,B_470] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_469,B_470,k1_xboole_0))
      | r2_hidden(B_470,'#skF_1'(A_469,B_470,k1_xboole_0))
      | ~ m1_subset_1(B_470,u1_struct_0(A_469))
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_407,c_12])).

tff(c_436,plain,(
    ! [B_470,A_469] :
      ( r2_hidden(B_470,'#skF_1'(A_469,B_470,k1_xboole_0))
      | ~ m1_subset_1(B_470,u1_struct_0(A_469))
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_416])).

tff(c_46,plain,(
    ! [A_22,B_30] :
      ( r2_hidden('#skF_1'(A_22,B_30,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc('#skF_1'(A_22,B_30,k1_xboole_0),A_22)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_94,plain,(
    ! [A_22,B_30] :
      ( r2_hidden('#skF_1'(A_22,B_30,k1_xboole_0),k1_xboole_0)
      | v3_pre_topc('#skF_1'(A_22,B_30,k1_xboole_0),A_22)
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_30,plain,(
    ! [A_22,B_30] :
      ( m1_subset_1('#skF_1'(A_22,B_30,k1_xboole_0),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_102,plain,(
    ! [A_22,B_30] :
      ( m1_subset_1('#skF_1'(A_22,B_30,k1_xboole_0),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_30,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_64,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_306,plain,(
    ! [B_447,A_448] :
      ( v3_pre_topc(B_447,g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448)))
      | ~ m1_subset_1(B_447,k1_zfmisc_1(u1_struct_0(A_448)))
      | ~ v3_pre_topc(B_447,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_309,plain,(
    ! [B_447] :
      ( v3_pre_topc(B_447,'#skF_5')
      | ~ m1_subset_1(B_447,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_447,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_306])).

tff(c_312,plain,(
    ! [B_449] :
      ( v3_pre_topc(B_449,'#skF_5')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_449,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_309])).

tff(c_316,plain,(
    ! [B_30] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_102,c_312])).

tff(c_327,plain,(
    ! [B_30] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_316])).

tff(c_328,plain,(
    ! [B_30] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_30,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_327])).

tff(c_291,plain,(
    ! [A_442,B_443] :
      ( m1_subset_1('#skF_1'(A_442,B_443,k1_xboole_0),k1_zfmisc_1(u1_struct_0(A_442)))
      | ~ m1_subset_1(B_443,u1_struct_0(A_442))
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_298,plain,(
    ! [A_442,B_443] :
      ( r1_tarski('#skF_1'(A_442,B_443,k1_xboole_0),u1_struct_0(A_442))
      | ~ m1_subset_1(B_443,u1_struct_0(A_442))
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_291,c_6])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_347,plain,(
    ! [B_452,A_453] :
      ( m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_453),u1_pre_topc(A_453)))))
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ v3_pre_topc(B_452,A_453)
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_355,plain,(
    ! [B_452] :
      ( m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_452,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_347])).

tff(c_360,plain,(
    ! [B_454] :
      ( m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_454,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_454,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_355])).

tff(c_368,plain,(
    ! [B_455] :
      ( r1_tarski(B_455,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_455,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_360,c_6])).

tff(c_385,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(A_3,'#skF_4')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_368])).

tff(c_48,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_176,plain,(
    ! [A_433,B_434] :
      ( m1_pre_topc(A_433,g1_pre_topc(u1_struct_0(B_434),u1_pre_topc(B_434)))
      | ~ m1_pre_topc(A_433,B_434)
      | ~ l1_pre_topc(B_434)
      | ~ l1_pre_topc(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_185,plain,(
    ! [A_433] :
      ( m1_pre_topc(A_433,'#skF_5')
      | ~ m1_pre_topc(A_433,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_176])).

tff(c_189,plain,(
    ! [A_433] :
      ( m1_pre_topc(A_433,'#skF_5')
      | ~ m1_pre_topc(A_433,'#skF_4')
      | ~ l1_pre_topc(A_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_185])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_58,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_54,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_92,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54])).

tff(c_82,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_72,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62])).

tff(c_56,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_987,plain,(
    ! [C_524,B_527,E_526,H_528,F_529,D_530,A_525] :
      ( r1_tmap_1(D_530,B_527,E_526,H_528)
      | ~ r1_tmap_1(C_524,B_527,k3_tmap_1(A_525,B_527,D_530,C_524,E_526),H_528)
      | ~ r1_tarski(F_529,u1_struct_0(C_524))
      | ~ r2_hidden(H_528,F_529)
      | ~ v3_pre_topc(F_529,D_530)
      | ~ m1_subset_1(H_528,u1_struct_0(C_524))
      | ~ m1_subset_1(H_528,u1_struct_0(D_530))
      | ~ m1_subset_1(F_529,k1_zfmisc_1(u1_struct_0(D_530)))
      | ~ m1_pre_topc(C_524,D_530)
      | ~ m1_subset_1(E_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_530),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_526,u1_struct_0(D_530),u1_struct_0(B_527))
      | ~ v1_funct_1(E_526)
      | ~ m1_pre_topc(D_530,A_525)
      | v2_struct_0(D_530)
      | ~ m1_pre_topc(C_524,A_525)
      | v2_struct_0(C_524)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_989,plain,(
    ! [F_529] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_529,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_529)
      | ~ v3_pre_topc(F_529,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_529,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_56,c_987])).

tff(c_992,plain,(
    ! [F_529] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_529,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_529)
      | ~ v3_pre_topc(F_529,'#skF_5')
      | ~ m1_subset_1(F_529,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_76,c_72,c_70,c_68,c_66,c_91,c_60,c_989])).

tff(c_993,plain,(
    ! [F_529] :
      ( ~ r1_tarski(F_529,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_529)
      | ~ v3_pre_topc(F_529,'#skF_5')
      | ~ m1_subset_1(F_529,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_78,c_74,c_92,c_992])).

tff(c_994,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_993])).

tff(c_997,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_994])).

tff(c_1000,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_997])).

tff(c_1003,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1000])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_1003])).

tff(c_1050,plain,(
    ! [F_537] :
      ( ~ r1_tarski(F_537,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_537)
      | ~ v3_pre_topc(F_537,'#skF_5')
      | ~ m1_subset_1(F_537,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_993])).

tff(c_1075,plain,(
    ! [A_538] :
      ( ~ r1_tarski(A_538,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',A_538)
      | ~ v3_pre_topc(A_538,'#skF_5')
      | ~ r1_tarski(A_538,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_8,c_1050])).

tff(c_1103,plain,(
    ! [A_539] :
      ( ~ r2_hidden('#skF_8',A_539)
      | ~ v3_pre_topc(A_539,'#skF_5')
      | ~ v3_pre_topc(A_539,'#skF_4')
      | ~ r1_tarski(A_539,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_385,c_1075])).

tff(c_1113,plain,(
    ! [B_443] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_443,k1_xboole_0))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_443,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_443,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_298,c_1103])).

tff(c_1122,plain,(
    ! [B_443] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_443,k1_xboole_0))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_443,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_443,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_1113])).

tff(c_1148,plain,(
    ! [B_542] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_542,k1_xboole_0))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_542,k1_xboole_0),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_542,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_542,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1122])).

tff(c_1153,plain,(
    ! [B_543] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_543,k1_xboole_0))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_543,k1_xboole_0),'#skF_4')
      | ~ m1_subset_1(B_543,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_328,c_1148])).

tff(c_1157,plain,(
    ! [B_30] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_30,k1_xboole_0))
      | r2_hidden('#skF_1'('#skF_4',B_30,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_94,c_1153])).

tff(c_1160,plain,(
    ! [B_30] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_30,k1_xboole_0))
      | r2_hidden('#skF_1'('#skF_4',B_30,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_1157])).

tff(c_1162,plain,(
    ! [B_544] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_544,k1_xboole_0))
      | r2_hidden('#skF_1'('#skF_4',B_544,k1_xboole_0),k1_xboole_0)
      | ~ m1_subset_1(B_544,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1160])).

tff(c_1177,plain,(
    ! [B_544] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'('#skF_4',B_544,k1_xboole_0))
      | ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_544,k1_xboole_0))
      | ~ m1_subset_1(B_544,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1162,c_12])).

tff(c_1197,plain,(
    ! [B_545] :
      ( ~ r2_hidden('#skF_8','#skF_1'('#skF_4',B_545,k1_xboole_0))
      | ~ m1_subset_1(B_545,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1177])).

tff(c_1201,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_436,c_1197])).

tff(c_1204,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_131,c_60,c_1201])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.70  
% 3.78/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.71  %$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.78/1.71  
% 3.78/1.71  %Foreground sorts:
% 3.78/1.71  
% 3.78/1.71  
% 3.78/1.71  %Background operators:
% 3.78/1.71  
% 3.78/1.71  
% 3.78/1.71  %Foreground operators:
% 3.78/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.78/1.71  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.78/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.78/1.71  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.78/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.78/1.71  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.78/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.71  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.78/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.71  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.78/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.78/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.78/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.78/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.78/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.78/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.78/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.71  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.78/1.71  tff('#skF_8', type, '#skF_8': $i).
% 3.78/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.78/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.78/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.78/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.71  
% 4.21/1.74  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.21/1.74  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.21/1.74  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.21/1.74  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.21/1.74  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.21/1.74  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 4.21/1.74  tff(f_44, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.21/1.74  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 4.21/1.74  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.21/1.74  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.21/1.74  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.21/1.74  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.21/1.74  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_88, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_86, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_76, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_147, plain, (![B_423, A_424]: (v2_pre_topc(B_423) | ~m1_pre_topc(B_423, A_424) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.21/1.74  tff(c_156, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_76, c_147])).
% 4.21/1.74  tff(c_163, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_156])).
% 4.21/1.74  tff(c_115, plain, (![B_417, A_418]: (l1_pre_topc(B_417) | ~m1_pre_topc(B_417, A_418) | ~l1_pre_topc(A_418))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.21/1.74  tff(c_124, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_76, c_115])).
% 4.21/1.74  tff(c_131, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_124])).
% 4.21/1.74  tff(c_60, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.21/1.74  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.21/1.74  tff(c_38, plain, (![A_22, B_30]: (r2_hidden('#skF_1'(A_22, B_30, k1_xboole_0), k1_xboole_0) | r2_hidden(B_30, '#skF_1'(A_22, B_30, k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.21/1.74  tff(c_407, plain, (![A_469, B_470]: (r2_hidden('#skF_1'(A_469, B_470, k1_xboole_0), k1_xboole_0) | r2_hidden(B_470, '#skF_1'(A_469, B_470, k1_xboole_0)) | ~m1_subset_1(B_470, u1_struct_0(A_469)) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_38])).
% 4.21/1.74  tff(c_12, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.21/1.74  tff(c_416, plain, (![A_469, B_470]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_469, B_470, k1_xboole_0)) | r2_hidden(B_470, '#skF_1'(A_469, B_470, k1_xboole_0)) | ~m1_subset_1(B_470, u1_struct_0(A_469)) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(resolution, [status(thm)], [c_407, c_12])).
% 4.21/1.74  tff(c_436, plain, (![B_470, A_469]: (r2_hidden(B_470, '#skF_1'(A_469, B_470, k1_xboole_0)) | ~m1_subset_1(B_470, u1_struct_0(A_469)) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_416])).
% 4.21/1.74  tff(c_46, plain, (![A_22, B_30]: (r2_hidden('#skF_1'(A_22, B_30, k1_xboole_0), k1_xboole_0) | v3_pre_topc('#skF_1'(A_22, B_30, k1_xboole_0), A_22) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.21/1.74  tff(c_94, plain, (![A_22, B_30]: (r2_hidden('#skF_1'(A_22, B_30, k1_xboole_0), k1_xboole_0) | v3_pre_topc('#skF_1'(A_22, B_30, k1_xboole_0), A_22) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 4.21/1.74  tff(c_30, plain, (![A_22, B_30]: (m1_subset_1('#skF_1'(A_22, B_30, k1_xboole_0), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.21/1.74  tff(c_102, plain, (![A_22, B_30]: (m1_subset_1('#skF_1'(A_22, B_30, k1_xboole_0), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_30, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_30])).
% 4.21/1.74  tff(c_64, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_306, plain, (![B_447, A_448]: (v3_pre_topc(B_447, g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))) | ~m1_subset_1(B_447, k1_zfmisc_1(u1_struct_0(A_448))) | ~v3_pre_topc(B_447, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.21/1.74  tff(c_309, plain, (![B_447]: (v3_pre_topc(B_447, '#skF_5') | ~m1_subset_1(B_447, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_447, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_306])).
% 4.21/1.74  tff(c_312, plain, (![B_449]: (v3_pre_topc(B_449, '#skF_5') | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_449, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_309])).
% 4.21/1.74  tff(c_316, plain, (![B_30]: (v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_30, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_312])).
% 4.21/1.74  tff(c_327, plain, (![B_30]: (v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_30, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_316])).
% 4.21/1.74  tff(c_328, plain, (![B_30]: (v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_30, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_30, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_327])).
% 4.21/1.74  tff(c_291, plain, (![A_442, B_443]: (m1_subset_1('#skF_1'(A_442, B_443, k1_xboole_0), k1_zfmisc_1(u1_struct_0(A_442))) | ~m1_subset_1(B_443, u1_struct_0(A_442)) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_30])).
% 4.21/1.74  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.21/1.74  tff(c_298, plain, (![A_442, B_443]: (r1_tarski('#skF_1'(A_442, B_443, k1_xboole_0), u1_struct_0(A_442)) | ~m1_subset_1(B_443, u1_struct_0(A_442)) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(resolution, [status(thm)], [c_291, c_6])).
% 4.21/1.74  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.21/1.74  tff(c_347, plain, (![B_452, A_453]: (m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_453), u1_pre_topc(A_453))))) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_453))) | ~v3_pre_topc(B_452, A_453) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.21/1.74  tff(c_355, plain, (![B_452]: (m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_452, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_347])).
% 4.21/1.74  tff(c_360, plain, (![B_454]: (m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_454, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_454, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_355])).
% 4.21/1.74  tff(c_368, plain, (![B_455]: (r1_tarski(B_455, u1_struct_0('#skF_5')) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_455, '#skF_4'))), inference(resolution, [status(thm)], [c_360, c_6])).
% 4.21/1.74  tff(c_385, plain, (![A_3]: (r1_tarski(A_3, u1_struct_0('#skF_5')) | ~v3_pre_topc(A_3, '#skF_4') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_368])).
% 4.21/1.74  tff(c_48, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.21/1.74  tff(c_176, plain, (![A_433, B_434]: (m1_pre_topc(A_433, g1_pre_topc(u1_struct_0(B_434), u1_pre_topc(B_434))) | ~m1_pre_topc(A_433, B_434) | ~l1_pre_topc(B_434) | ~l1_pre_topc(A_433))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.21/1.74  tff(c_185, plain, (![A_433]: (m1_pre_topc(A_433, '#skF_5') | ~m1_pre_topc(A_433, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_433))), inference(superposition, [status(thm), theory('equality')], [c_64, c_176])).
% 4.21/1.74  tff(c_189, plain, (![A_433]: (m1_pre_topc(A_433, '#skF_5') | ~m1_pre_topc(A_433, '#skF_4') | ~l1_pre_topc(A_433))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_185])).
% 4.21/1.74  tff(c_90, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_84, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_58, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_54, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_92, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54])).
% 4.21/1.74  tff(c_82, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_72, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_68, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_62, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62])).
% 4.21/1.74  tff(c_56, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.21/1.74  tff(c_987, plain, (![C_524, B_527, E_526, H_528, F_529, D_530, A_525]: (r1_tmap_1(D_530, B_527, E_526, H_528) | ~r1_tmap_1(C_524, B_527, k3_tmap_1(A_525, B_527, D_530, C_524, E_526), H_528) | ~r1_tarski(F_529, u1_struct_0(C_524)) | ~r2_hidden(H_528, F_529) | ~v3_pre_topc(F_529, D_530) | ~m1_subset_1(H_528, u1_struct_0(C_524)) | ~m1_subset_1(H_528, u1_struct_0(D_530)) | ~m1_subset_1(F_529, k1_zfmisc_1(u1_struct_0(D_530))) | ~m1_pre_topc(C_524, D_530) | ~m1_subset_1(E_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_530), u1_struct_0(B_527)))) | ~v1_funct_2(E_526, u1_struct_0(D_530), u1_struct_0(B_527)) | ~v1_funct_1(E_526) | ~m1_pre_topc(D_530, A_525) | v2_struct_0(D_530) | ~m1_pre_topc(C_524, A_525) | v2_struct_0(C_524) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.21/1.74  tff(c_989, plain, (![F_529]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_529, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_529) | ~v3_pre_topc(F_529, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_529, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_987])).
% 4.21/1.74  tff(c_992, plain, (![F_529]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_529, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_529) | ~v3_pre_topc(F_529, '#skF_5') | ~m1_subset_1(F_529, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_80, c_76, c_72, c_70, c_68, c_66, c_91, c_60, c_989])).
% 4.21/1.74  tff(c_993, plain, (![F_529]: (~r1_tarski(F_529, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_529) | ~v3_pre_topc(F_529, '#skF_5') | ~m1_subset_1(F_529, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_78, c_74, c_92, c_992])).
% 4.21/1.74  tff(c_994, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_993])).
% 4.21/1.74  tff(c_997, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_189, c_994])).
% 4.21/1.74  tff(c_1000, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_997])).
% 4.21/1.74  tff(c_1003, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1000])).
% 4.21/1.74  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_1003])).
% 4.21/1.74  tff(c_1050, plain, (![F_537]: (~r1_tarski(F_537, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_537) | ~v3_pre_topc(F_537, '#skF_5') | ~m1_subset_1(F_537, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_993])).
% 4.21/1.74  tff(c_1075, plain, (![A_538]: (~r1_tarski(A_538, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', A_538) | ~v3_pre_topc(A_538, '#skF_5') | ~r1_tarski(A_538, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_8, c_1050])).
% 4.21/1.74  tff(c_1103, plain, (![A_539]: (~r2_hidden('#skF_8', A_539) | ~v3_pre_topc(A_539, '#skF_5') | ~v3_pre_topc(A_539, '#skF_4') | ~r1_tarski(A_539, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_385, c_1075])).
% 4.21/1.74  tff(c_1113, plain, (![B_443]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_443, k1_xboole_0)) | ~v3_pre_topc('#skF_1'('#skF_4', B_443, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_443, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_443, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_298, c_1103])).
% 4.21/1.74  tff(c_1122, plain, (![B_443]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_443, k1_xboole_0)) | ~v3_pre_topc('#skF_1'('#skF_4', B_443, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_443, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_443, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_1113])).
% 4.21/1.74  tff(c_1148, plain, (![B_542]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_542, k1_xboole_0)) | ~v3_pre_topc('#skF_1'('#skF_4', B_542, k1_xboole_0), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_542, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_542, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1122])).
% 4.21/1.74  tff(c_1153, plain, (![B_543]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_543, k1_xboole_0)) | ~v3_pre_topc('#skF_1'('#skF_4', B_543, k1_xboole_0), '#skF_4') | ~m1_subset_1(B_543, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_328, c_1148])).
% 4.21/1.74  tff(c_1157, plain, (![B_30]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_30, k1_xboole_0)) | r2_hidden('#skF_1'('#skF_4', B_30, k1_xboole_0), k1_xboole_0) | ~m1_subset_1(B_30, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_94, c_1153])).
% 4.21/1.74  tff(c_1160, plain, (![B_30]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_30, k1_xboole_0)) | r2_hidden('#skF_1'('#skF_4', B_30, k1_xboole_0), k1_xboole_0) | ~m1_subset_1(B_30, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_1157])).
% 4.21/1.74  tff(c_1162, plain, (![B_544]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_544, k1_xboole_0)) | r2_hidden('#skF_1'('#skF_4', B_544, k1_xboole_0), k1_xboole_0) | ~m1_subset_1(B_544, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1160])).
% 4.21/1.74  tff(c_1177, plain, (![B_544]: (~r1_tarski(k1_xboole_0, '#skF_1'('#skF_4', B_544, k1_xboole_0)) | ~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_544, k1_xboole_0)) | ~m1_subset_1(B_544, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1162, c_12])).
% 4.21/1.74  tff(c_1197, plain, (![B_545]: (~r2_hidden('#skF_8', '#skF_1'('#skF_4', B_545, k1_xboole_0)) | ~m1_subset_1(B_545, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1177])).
% 4.21/1.74  tff(c_1201, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_436, c_1197])).
% 4.21/1.74  tff(c_1204, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_131, c_60, c_1201])).
% 4.21/1.74  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1204])).
% 4.21/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.74  
% 4.21/1.74  Inference rules
% 4.21/1.74  ----------------------
% 4.21/1.74  #Ref     : 0
% 4.21/1.74  #Sup     : 199
% 4.21/1.74  #Fact    : 0
% 4.21/1.74  #Define  : 0
% 4.21/1.74  #Split   : 6
% 4.21/1.74  #Chain   : 0
% 4.21/1.74  #Close   : 0
% 4.21/1.74  
% 4.21/1.74  Ordering : KBO
% 4.21/1.74  
% 4.21/1.74  Simplification rules
% 4.21/1.74  ----------------------
% 4.21/1.74  #Subsume      : 55
% 4.21/1.74  #Demod        : 198
% 4.21/1.74  #Tautology    : 52
% 4.21/1.74  #SimpNegUnit  : 39
% 4.21/1.74  #BackRed      : 0
% 4.21/1.74  
% 4.21/1.74  #Partial instantiations: 0
% 4.21/1.74  #Strategies tried      : 1
% 4.21/1.74  
% 4.21/1.74  Timing (in seconds)
% 4.21/1.74  ----------------------
% 4.21/1.74  Preprocessing        : 0.42
% 4.21/1.74  Parsing              : 0.21
% 4.21/1.74  CNF conversion       : 0.06
% 4.21/1.74  Main loop            : 0.48
% 4.21/1.74  Inferencing          : 0.17
% 4.21/1.75  Reduction            : 0.15
% 4.21/1.75  Demodulation         : 0.11
% 4.21/1.75  BG Simplification    : 0.03
% 4.21/1.75  Subsumption          : 0.11
% 4.21/1.75  Abstraction          : 0.02
% 4.21/1.75  MUC search           : 0.00
% 4.21/1.75  Cooper               : 0.00
% 4.21/1.75  Total                : 0.95
% 4.21/1.75  Index Insertion      : 0.00
% 4.21/1.75  Index Deletion       : 0.00
% 4.21/1.75  Index Matching       : 0.00
% 4.21/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
