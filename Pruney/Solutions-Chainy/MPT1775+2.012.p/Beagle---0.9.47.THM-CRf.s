%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 622 expanded)
%              Number of leaves         :   45 ( 254 expanded)
%              Depth                    :   15
%              Number of atoms          :  393 (4559 expanded)
%              Number of equality atoms :    7 ( 212 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_110,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_232,axiom,(
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

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_85,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_103,plain,(
    ! [B_548,A_549] :
      ( l1_pre_topc(B_548)
      | ~ m1_pre_topc(B_548,A_549)
      | ~ l1_pre_topc(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_118,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_109])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_115,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_106])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_180,plain,(
    ! [B_568,A_569] :
      ( m1_subset_1(u1_struct_0(B_568),k1_zfmisc_1(u1_struct_0(A_569)))
      | ~ m1_pre_topc(B_568,A_569)
      | ~ l1_pre_topc(A_569) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_239,plain,(
    ! [A_581,A_582,B_583] :
      ( m1_subset_1(A_581,u1_struct_0(A_582))
      | ~ r2_hidden(A_581,u1_struct_0(B_583))
      | ~ m1_pre_topc(B_583,A_582)
      | ~ l1_pre_topc(A_582) ) ),
    inference(resolution,[status(thm)],[c_180,c_12])).

tff(c_246,plain,(
    ! [A_584,A_585,B_586] :
      ( m1_subset_1(A_584,u1_struct_0(A_585))
      | ~ m1_pre_topc(B_586,A_585)
      | ~ l1_pre_topc(A_585)
      | v1_xboole_0(u1_struct_0(B_586))
      | ~ m1_subset_1(A_584,u1_struct_0(B_586)) ) ),
    inference(resolution,[status(thm)],[c_6,c_239])).

tff(c_256,plain,(
    ! [A_584] :
      ( m1_subset_1(A_584,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_584,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_267,plain,(
    ! [A_584] :
      ( m1_subset_1(A_584,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_584,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_256])).

tff(c_299,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_20,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_302,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_20])).

tff(c_305,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_302])).

tff(c_308,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_308])).

tff(c_314,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_138,plain,(
    ! [B_557,A_558] :
      ( v2_pre_topc(B_557)
      | ~ m1_pre_topc(B_557,A_558)
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_138])).

tff(c_150,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_141])).

tff(c_48,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_30,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_327,plain,(
    ! [B_592,A_593] :
      ( v3_pre_topc(u1_struct_0(B_592),A_593)
      | ~ v1_tsep_1(B_592,A_593)
      | ~ m1_subset_1(u1_struct_0(B_592),k1_zfmisc_1(u1_struct_0(A_593)))
      | ~ m1_pre_topc(B_592,A_593)
      | ~ l1_pre_topc(A_593)
      | ~ v2_pre_topc(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_338,plain,(
    ! [B_34,A_32] :
      ( v3_pre_topc(u1_struct_0(B_34),A_32)
      | ~ v1_tsep_1(B_34,A_32)
      | ~ v2_pre_topc(A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_187,plain,(
    ! [B_568,A_569] :
      ( r1_tarski(u1_struct_0(B_568),u1_struct_0(A_569))
      | ~ m1_pre_topc(B_568,A_569)
      | ~ l1_pre_topc(A_569) ) ),
    inference(resolution,[status(thm)],[c_180,c_8])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_123,plain,(
    ! [A_552,B_553] :
      ( r1_tarski(A_552,B_553)
      | ~ m1_subset_1(A_552,k1_zfmisc_1(B_553)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_86,c_123])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_179,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_245,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_84])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_593,plain,(
    ! [A_622,H_626,B_623,E_628,D_625,C_627,F_624] :
      ( r1_tmap_1(D_625,B_623,E_628,H_626)
      | ~ r1_tmap_1(C_627,B_623,k3_tmap_1(A_622,B_623,D_625,C_627,E_628),H_626)
      | ~ m1_connsp_2(F_624,D_625,H_626)
      | ~ r1_tarski(F_624,u1_struct_0(C_627))
      | ~ m1_subset_1(H_626,u1_struct_0(C_627))
      | ~ m1_subset_1(H_626,u1_struct_0(D_625))
      | ~ m1_subset_1(F_624,k1_zfmisc_1(u1_struct_0(D_625)))
      | ~ m1_pre_topc(C_627,D_625)
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_625),u1_struct_0(B_623))))
      | ~ v1_funct_2(E_628,u1_struct_0(D_625),u1_struct_0(B_623))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc(D_625,A_622)
      | v2_struct_0(D_625)
      | ~ m1_pre_topc(C_627,A_622)
      | v2_struct_0(C_627)
      | ~ l1_pre_topc(B_623)
      | ~ v2_pre_topc(B_623)
      | v2_struct_0(B_623)
      | ~ l1_pre_topc(A_622)
      | ~ v2_pre_topc(A_622)
      | v2_struct_0(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_595,plain,(
    ! [F_624] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_624,'#skF_4','#skF_6')
      | ~ r1_tarski(F_624,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_624,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_179,c_593])).

tff(c_598,plain,(
    ! [F_624] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_624,'#skF_4','#skF_6')
      | ~ r1_tarski(F_624,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_624,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_46,c_44,c_85,c_595])).

tff(c_600,plain,(
    ! [F_629] :
      ( ~ m1_connsp_2(F_629,'#skF_4','#skF_6')
      | ~ r1_tarski(F_629,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_629,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_245,c_598])).

tff(c_643,plain,(
    ! [A_631] :
      ( ~ m1_connsp_2(A_631,'#skF_4','#skF_6')
      | ~ r1_tarski(A_631,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_631,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_600])).

tff(c_655,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_3'),'#skF_4','#skF_6')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_131,c_643])).

tff(c_656,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_659,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_656])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_46,c_659])).

tff(c_664,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_3'),'#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_665,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_483,plain,(
    ! [B_611,A_612,C_613] :
      ( m1_connsp_2(B_611,A_612,C_613)
      | ~ r2_hidden(C_613,B_611)
      | ~ v3_pre_topc(B_611,A_612)
      | ~ m1_subset_1(C_613,u1_struct_0(A_612))
      | ~ m1_subset_1(B_611,k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_495,plain,(
    ! [B_611] :
      ( m1_connsp_2(B_611,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_611)
      | ~ v3_pre_topc(B_611,'#skF_4')
      | ~ m1_subset_1(B_611,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_483])).

tff(c_512,plain,(
    ! [B_611] :
      ( m1_connsp_2(B_611,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_611)
      | ~ v3_pre_topc(B_611,'#skF_4')
      | ~ m1_subset_1(B_611,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_115,c_495])).

tff(c_567,plain,(
    ! [B_621] :
      ( m1_connsp_2(B_621,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_621)
      | ~ v3_pre_topc(B_621,'#skF_4')
      | ~ m1_subset_1(B_621,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_512])).

tff(c_757,plain,(
    ! [A_647] :
      ( m1_connsp_2(A_647,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',A_647)
      | ~ v3_pre_topc(A_647,'#skF_4')
      | ~ r1_tarski(A_647,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_567])).

tff(c_760,plain,
    ( m1_connsp_2(u1_struct_0('#skF_3'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_665,c_757])).

tff(c_771,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_760])).

tff(c_776,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_792,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_776])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_46,c_150,c_48,c_792])).

tff(c_797,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_807,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_797])).

tff(c_810,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_807])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_810])).

tff(c_813,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1089,plain,(
    ! [E_688,D_690,G_691,B_689,C_686,A_687] :
      ( r1_tmap_1(D_690,B_689,k3_tmap_1(A_687,B_689,C_686,D_690,E_688),G_691)
      | ~ r1_tmap_1(C_686,B_689,E_688,G_691)
      | ~ m1_pre_topc(D_690,C_686)
      | ~ m1_subset_1(G_691,u1_struct_0(D_690))
      | ~ m1_subset_1(G_691,u1_struct_0(C_686))
      | ~ m1_subset_1(E_688,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_686),u1_struct_0(B_689))))
      | ~ v1_funct_2(E_688,u1_struct_0(C_686),u1_struct_0(B_689))
      | ~ v1_funct_1(E_688)
      | ~ m1_pre_topc(D_690,A_687)
      | v2_struct_0(D_690)
      | ~ m1_pre_topc(C_686,A_687)
      | v2_struct_0(C_686)
      | ~ l1_pre_topc(B_689)
      | ~ v2_pre_topc(B_689)
      | v2_struct_0(B_689)
      | ~ l1_pre_topc(A_687)
      | ~ v2_pre_topc(A_687)
      | v2_struct_0(A_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1091,plain,(
    ! [D_690,A_687,G_691] :
      ( r1_tmap_1(D_690,'#skF_2',k3_tmap_1(A_687,'#skF_2','#skF_4',D_690,'#skF_5'),G_691)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_691)
      | ~ m1_pre_topc(D_690,'#skF_4')
      | ~ m1_subset_1(G_691,u1_struct_0(D_690))
      | ~ m1_subset_1(G_691,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_690,A_687)
      | v2_struct_0(D_690)
      | ~ m1_pre_topc('#skF_4',A_687)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_687)
      | ~ v2_pre_topc(A_687)
      | v2_struct_0(A_687) ) ),
    inference(resolution,[status(thm)],[c_50,c_1089])).

tff(c_1100,plain,(
    ! [D_690,A_687,G_691] :
      ( r1_tmap_1(D_690,'#skF_2',k3_tmap_1(A_687,'#skF_2','#skF_4',D_690,'#skF_5'),G_691)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_691)
      | ~ m1_pre_topc(D_690,'#skF_4')
      | ~ m1_subset_1(G_691,u1_struct_0(D_690))
      | ~ m1_subset_1(G_691,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_690,A_687)
      | v2_struct_0(D_690)
      | ~ m1_pre_topc('#skF_4',A_687)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_687)
      | ~ v2_pre_topc(A_687)
      | v2_struct_0(A_687) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_1091])).

tff(c_1222,plain,(
    ! [D_710,A_711,G_712] :
      ( r1_tmap_1(D_710,'#skF_2',k3_tmap_1(A_711,'#skF_2','#skF_4',D_710,'#skF_5'),G_712)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_712)
      | ~ m1_pre_topc(D_710,'#skF_4')
      | ~ m1_subset_1(G_712,u1_struct_0(D_710))
      | ~ m1_subset_1(G_712,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_710,A_711)
      | v2_struct_0(D_710)
      | ~ m1_pre_topc('#skF_4',A_711)
      | ~ l1_pre_topc(A_711)
      | ~ v2_pre_topc(A_711)
      | v2_struct_0(A_711) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_1100])).

tff(c_814,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1227,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1222,c_814])).

tff(c_1234,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_44,c_85,c_46,c_813,c_1227])).

tff(c_1236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_1234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.70  
% 4.22/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.70  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.22/1.70  
% 4.22/1.70  %Foreground sorts:
% 4.22/1.70  
% 4.22/1.70  
% 4.22/1.70  %Background operators:
% 4.22/1.70  
% 4.22/1.70  
% 4.22/1.70  %Foreground operators:
% 4.22/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.22/1.70  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.22/1.70  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.22/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.22/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.22/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.70  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.22/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.22/1.70  tff('#skF_7', type, '#skF_7': $i).
% 4.22/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.22/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.22/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.22/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.22/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.22/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.22/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.22/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.22/1.70  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.22/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.22/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.22/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.22/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.22/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.22/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.22/1.70  
% 4.22/1.73  tff(f_283, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.22/1.73  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.22/1.73  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.22/1.73  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.22/1.73  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.22/1.73  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.22/1.73  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.22/1.73  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.22/1.73  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.22/1.73  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.22/1.73  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.22/1.73  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.22/1.73  tff(f_232, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.22/1.73  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.22/1.73  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.22/1.73  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_85, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 4.22/1.73  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_103, plain, (![B_548, A_549]: (l1_pre_topc(B_548) | ~m1_pre_topc(B_548, A_549) | ~l1_pre_topc(A_549))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.22/1.73  tff(c_109, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_103])).
% 4.22/1.73  tff(c_118, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_109])).
% 4.22/1.73  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.22/1.73  tff(c_106, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_103])).
% 4.22/1.73  tff(c_115, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_106])).
% 4.22/1.73  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.22/1.73  tff(c_180, plain, (![B_568, A_569]: (m1_subset_1(u1_struct_0(B_568), k1_zfmisc_1(u1_struct_0(A_569))) | ~m1_pre_topc(B_568, A_569) | ~l1_pre_topc(A_569))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.73  tff(c_12, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.22/1.73  tff(c_239, plain, (![A_581, A_582, B_583]: (m1_subset_1(A_581, u1_struct_0(A_582)) | ~r2_hidden(A_581, u1_struct_0(B_583)) | ~m1_pre_topc(B_583, A_582) | ~l1_pre_topc(A_582))), inference(resolution, [status(thm)], [c_180, c_12])).
% 4.22/1.73  tff(c_246, plain, (![A_584, A_585, B_586]: (m1_subset_1(A_584, u1_struct_0(A_585)) | ~m1_pre_topc(B_586, A_585) | ~l1_pre_topc(A_585) | v1_xboole_0(u1_struct_0(B_586)) | ~m1_subset_1(A_584, u1_struct_0(B_586)))), inference(resolution, [status(thm)], [c_6, c_239])).
% 4.22/1.73  tff(c_256, plain, (![A_584]: (m1_subset_1(A_584, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_584, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_246])).
% 4.22/1.73  tff(c_267, plain, (![A_584]: (m1_subset_1(A_584, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_584, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_256])).
% 4.22/1.73  tff(c_299, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_267])).
% 4.22/1.73  tff(c_20, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.22/1.73  tff(c_302, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_299, c_20])).
% 4.22/1.73  tff(c_305, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_302])).
% 4.22/1.73  tff(c_308, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_305])).
% 4.22/1.73  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_308])).
% 4.22/1.73  tff(c_314, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_267])).
% 4.22/1.73  tff(c_138, plain, (![B_557, A_558]: (v2_pre_topc(B_557) | ~m1_pre_topc(B_557, A_558) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.22/1.73  tff(c_141, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_138])).
% 4.22/1.73  tff(c_150, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_141])).
% 4.22/1.73  tff(c_48, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_30, plain, (![B_34, A_32]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.73  tff(c_327, plain, (![B_592, A_593]: (v3_pre_topc(u1_struct_0(B_592), A_593) | ~v1_tsep_1(B_592, A_593) | ~m1_subset_1(u1_struct_0(B_592), k1_zfmisc_1(u1_struct_0(A_593))) | ~m1_pre_topc(B_592, A_593) | ~l1_pre_topc(A_593) | ~v2_pre_topc(A_593))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.22/1.73  tff(c_338, plain, (![B_34, A_32]: (v3_pre_topc(u1_struct_0(B_34), A_32) | ~v1_tsep_1(B_34, A_32) | ~v2_pre_topc(A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_30, c_327])).
% 4.22/1.73  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.73  tff(c_187, plain, (![B_568, A_569]: (r1_tarski(u1_struct_0(B_568), u1_struct_0(A_569)) | ~m1_pre_topc(B_568, A_569) | ~l1_pre_topc(A_569))), inference(resolution, [status(thm)], [c_180, c_8])).
% 4.22/1.73  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.22/1.73  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.22/1.73  tff(c_86, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.22/1.73  tff(c_123, plain, (![A_552, B_553]: (r1_tarski(A_552, B_553) | ~m1_subset_1(A_552, k1_zfmisc_1(B_553)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.73  tff(c_131, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_86, c_123])).
% 4.22/1.73  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.22/1.73  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 4.22/1.73  tff(c_179, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_83])).
% 4.22/1.73  tff(c_76, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_84, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 4.22/1.73  tff(c_245, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_84])).
% 4.22/1.73  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.22/1.73  tff(c_593, plain, (![A_622, H_626, B_623, E_628, D_625, C_627, F_624]: (r1_tmap_1(D_625, B_623, E_628, H_626) | ~r1_tmap_1(C_627, B_623, k3_tmap_1(A_622, B_623, D_625, C_627, E_628), H_626) | ~m1_connsp_2(F_624, D_625, H_626) | ~r1_tarski(F_624, u1_struct_0(C_627)) | ~m1_subset_1(H_626, u1_struct_0(C_627)) | ~m1_subset_1(H_626, u1_struct_0(D_625)) | ~m1_subset_1(F_624, k1_zfmisc_1(u1_struct_0(D_625))) | ~m1_pre_topc(C_627, D_625) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_625), u1_struct_0(B_623)))) | ~v1_funct_2(E_628, u1_struct_0(D_625), u1_struct_0(B_623)) | ~v1_funct_1(E_628) | ~m1_pre_topc(D_625, A_622) | v2_struct_0(D_625) | ~m1_pre_topc(C_627, A_622) | v2_struct_0(C_627) | ~l1_pre_topc(B_623) | ~v2_pre_topc(B_623) | v2_struct_0(B_623) | ~l1_pre_topc(A_622) | ~v2_pre_topc(A_622) | v2_struct_0(A_622))), inference(cnfTransformation, [status(thm)], [f_232])).
% 4.22/1.73  tff(c_595, plain, (![F_624]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_624, '#skF_4', '#skF_6') | ~r1_tarski(F_624, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_624, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_179, c_593])).
% 4.22/1.73  tff(c_598, plain, (![F_624]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_624, '#skF_4', '#skF_6') | ~r1_tarski(F_624, u1_struct_0('#skF_3')) | ~m1_subset_1(F_624, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_46, c_44, c_85, c_595])).
% 4.22/1.73  tff(c_600, plain, (![F_629]: (~m1_connsp_2(F_629, '#skF_4', '#skF_6') | ~r1_tarski(F_629, u1_struct_0('#skF_3')) | ~m1_subset_1(F_629, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_245, c_598])).
% 4.22/1.73  tff(c_643, plain, (![A_631]: (~m1_connsp_2(A_631, '#skF_4', '#skF_6') | ~r1_tarski(A_631, u1_struct_0('#skF_3')) | ~r1_tarski(A_631, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_600])).
% 4.22/1.73  tff(c_655, plain, (~m1_connsp_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_6') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_131, c_643])).
% 4.22/1.73  tff(c_656, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_655])).
% 4.22/1.73  tff(c_659, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_187, c_656])).
% 4.22/1.73  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_46, c_659])).
% 4.22/1.73  tff(c_664, plain, (~m1_connsp_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_655])).
% 4.22/1.73  tff(c_665, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_655])).
% 4.22/1.73  tff(c_483, plain, (![B_611, A_612, C_613]: (m1_connsp_2(B_611, A_612, C_613) | ~r2_hidden(C_613, B_611) | ~v3_pre_topc(B_611, A_612) | ~m1_subset_1(C_613, u1_struct_0(A_612)) | ~m1_subset_1(B_611, k1_zfmisc_1(u1_struct_0(A_612))) | ~l1_pre_topc(A_612) | ~v2_pre_topc(A_612) | v2_struct_0(A_612))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.22/1.73  tff(c_495, plain, (![B_611]: (m1_connsp_2(B_611, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_611) | ~v3_pre_topc(B_611, '#skF_4') | ~m1_subset_1(B_611, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_483])).
% 4.22/1.73  tff(c_512, plain, (![B_611]: (m1_connsp_2(B_611, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_611) | ~v3_pre_topc(B_611, '#skF_4') | ~m1_subset_1(B_611, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_115, c_495])).
% 4.22/1.73  tff(c_567, plain, (![B_621]: (m1_connsp_2(B_621, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_621) | ~v3_pre_topc(B_621, '#skF_4') | ~m1_subset_1(B_621, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_512])).
% 4.22/1.73  tff(c_757, plain, (![A_647]: (m1_connsp_2(A_647, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', A_647) | ~v3_pre_topc(A_647, '#skF_4') | ~r1_tarski(A_647, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_567])).
% 4.22/1.73  tff(c_760, plain, (m1_connsp_2(u1_struct_0('#skF_3'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_665, c_757])).
% 4.22/1.73  tff(c_771, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_664, c_760])).
% 4.22/1.73  tff(c_776, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_771])).
% 4.22/1.73  tff(c_792, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_338, c_776])).
% 4.22/1.73  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_46, c_150, c_48, c_792])).
% 4.22/1.73  tff(c_797, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_771])).
% 4.22/1.73  tff(c_807, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_797])).
% 4.22/1.73  tff(c_810, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_807])).
% 4.22/1.73  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_810])).
% 4.22/1.73  tff(c_813, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 4.22/1.73  tff(c_1089, plain, (![E_688, D_690, G_691, B_689, C_686, A_687]: (r1_tmap_1(D_690, B_689, k3_tmap_1(A_687, B_689, C_686, D_690, E_688), G_691) | ~r1_tmap_1(C_686, B_689, E_688, G_691) | ~m1_pre_topc(D_690, C_686) | ~m1_subset_1(G_691, u1_struct_0(D_690)) | ~m1_subset_1(G_691, u1_struct_0(C_686)) | ~m1_subset_1(E_688, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_686), u1_struct_0(B_689)))) | ~v1_funct_2(E_688, u1_struct_0(C_686), u1_struct_0(B_689)) | ~v1_funct_1(E_688) | ~m1_pre_topc(D_690, A_687) | v2_struct_0(D_690) | ~m1_pre_topc(C_686, A_687) | v2_struct_0(C_686) | ~l1_pre_topc(B_689) | ~v2_pre_topc(B_689) | v2_struct_0(B_689) | ~l1_pre_topc(A_687) | ~v2_pre_topc(A_687) | v2_struct_0(A_687))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.22/1.73  tff(c_1091, plain, (![D_690, A_687, G_691]: (r1_tmap_1(D_690, '#skF_2', k3_tmap_1(A_687, '#skF_2', '#skF_4', D_690, '#skF_5'), G_691) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_691) | ~m1_pre_topc(D_690, '#skF_4') | ~m1_subset_1(G_691, u1_struct_0(D_690)) | ~m1_subset_1(G_691, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_690, A_687) | v2_struct_0(D_690) | ~m1_pre_topc('#skF_4', A_687) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_687) | ~v2_pre_topc(A_687) | v2_struct_0(A_687))), inference(resolution, [status(thm)], [c_50, c_1089])).
% 4.22/1.73  tff(c_1100, plain, (![D_690, A_687, G_691]: (r1_tmap_1(D_690, '#skF_2', k3_tmap_1(A_687, '#skF_2', '#skF_4', D_690, '#skF_5'), G_691) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_691) | ~m1_pre_topc(D_690, '#skF_4') | ~m1_subset_1(G_691, u1_struct_0(D_690)) | ~m1_subset_1(G_691, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_690, A_687) | v2_struct_0(D_690) | ~m1_pre_topc('#skF_4', A_687) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_687) | ~v2_pre_topc(A_687) | v2_struct_0(A_687))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_1091])).
% 4.22/1.73  tff(c_1222, plain, (![D_710, A_711, G_712]: (r1_tmap_1(D_710, '#skF_2', k3_tmap_1(A_711, '#skF_2', '#skF_4', D_710, '#skF_5'), G_712) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_712) | ~m1_pre_topc(D_710, '#skF_4') | ~m1_subset_1(G_712, u1_struct_0(D_710)) | ~m1_subset_1(G_712, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_710, A_711) | v2_struct_0(D_710) | ~m1_pre_topc('#skF_4', A_711) | ~l1_pre_topc(A_711) | ~v2_pre_topc(A_711) | v2_struct_0(A_711))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_1100])).
% 4.22/1.73  tff(c_814, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 4.22/1.73  tff(c_1227, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1222, c_814])).
% 4.22/1.73  tff(c_1234, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_44, c_85, c_46, c_813, c_1227])).
% 4.22/1.73  tff(c_1236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_1234])).
% 4.22/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.73  
% 4.22/1.73  Inference rules
% 4.22/1.73  ----------------------
% 4.22/1.73  #Ref     : 0
% 4.22/1.73  #Sup     : 203
% 4.22/1.73  #Fact    : 0
% 4.22/1.73  #Define  : 0
% 4.22/1.73  #Split   : 22
% 4.22/1.73  #Chain   : 0
% 4.22/1.73  #Close   : 0
% 4.22/1.73  
% 4.22/1.73  Ordering : KBO
% 4.22/1.73  
% 4.22/1.73  Simplification rules
% 4.22/1.73  ----------------------
% 4.22/1.73  #Subsume      : 46
% 4.22/1.73  #Demod        : 242
% 4.22/1.73  #Tautology    : 43
% 4.22/1.73  #SimpNegUnit  : 26
% 4.22/1.73  #BackRed      : 0
% 4.22/1.73  
% 4.22/1.73  #Partial instantiations: 0
% 4.22/1.73  #Strategies tried      : 1
% 4.22/1.73  
% 4.22/1.73  Timing (in seconds)
% 4.22/1.73  ----------------------
% 4.22/1.73  Preprocessing        : 0.42
% 4.22/1.73  Parsing              : 0.21
% 4.22/1.73  CNF conversion       : 0.06
% 4.22/1.73  Main loop            : 0.49
% 4.22/1.73  Inferencing          : 0.18
% 4.22/1.73  Reduction            : 0.16
% 4.22/1.73  Demodulation         : 0.11
% 4.22/1.73  BG Simplification    : 0.03
% 4.22/1.73  Subsumption          : 0.09
% 4.22/1.73  Abstraction          : 0.02
% 4.22/1.73  MUC search           : 0.00
% 4.22/1.73  Cooper               : 0.00
% 4.22/1.73  Total                : 0.97
% 4.22/1.73  Index Insertion      : 0.00
% 4.22/1.73  Index Deletion       : 0.00
% 4.22/1.74  Index Matching       : 0.00
% 4.22/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
