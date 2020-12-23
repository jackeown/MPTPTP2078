%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 312 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  333 (2336 expanded)
%              Number of equality atoms :    6 ( 109 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_265,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_90,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_214,axiom,(
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

tff(f_157,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_492,plain,(
    ! [B_619,A_620] :
      ( l1_pre_topc(B_619)
      | ~ m1_pre_topc(B_619,A_620)
      | ~ l1_pre_topc(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_498,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_492])).

tff(c_507,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_498])).

tff(c_18,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_85,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_93,plain,(
    ! [B_534,A_535] :
      ( v1_xboole_0(B_534)
      | ~ m1_subset_1(B_534,A_535)
      | ~ v1_xboole_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_85,c_93])).

tff(c_106,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [B_539,A_540] :
      ( l1_pre_topc(B_539)
      | ~ m1_pre_topc(B_539,A_540)
      | ~ l1_pre_topc(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_126,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_117])).

tff(c_147,plain,(
    ! [B_547,A_548] :
      ( v2_pre_topc(B_547)
      | ~ m1_pre_topc(B_547,A_548)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_147])).

tff(c_159,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_150])).

tff(c_48,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_30,plain,(
    ! [B_22,A_20] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_279,plain,(
    ! [B_567,A_568] :
      ( v3_pre_topc(u1_struct_0(B_567),A_568)
      | ~ v1_tsep_1(B_567,A_568)
      | ~ m1_subset_1(u1_struct_0(B_567),k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ m1_pre_topc(B_567,A_568)
      | ~ l1_pre_topc(A_568)
      | ~ v2_pre_topc(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_286,plain,(
    ! [B_22,A_20] :
      ( v3_pre_topc(u1_struct_0(B_22),A_20)
      | ~ v1_tsep_1(B_22,A_20)
      | ~ v2_pre_topc(A_20)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_30,c_279])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_200,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_216,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_84])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_305,plain,(
    ! [H_583,F_585,A_586,D_580,C_581,B_582,E_584] :
      ( r1_tmap_1(D_580,B_582,E_584,H_583)
      | ~ r1_tmap_1(C_581,B_582,k3_tmap_1(A_586,B_582,D_580,C_581,E_584),H_583)
      | ~ r1_tarski(F_585,u1_struct_0(C_581))
      | ~ r2_hidden(H_583,F_585)
      | ~ v3_pre_topc(F_585,D_580)
      | ~ m1_subset_1(H_583,u1_struct_0(C_581))
      | ~ m1_subset_1(H_583,u1_struct_0(D_580))
      | ~ m1_subset_1(F_585,k1_zfmisc_1(u1_struct_0(D_580)))
      | ~ m1_pre_topc(C_581,D_580)
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_580),u1_struct_0(B_582))))
      | ~ v1_funct_2(E_584,u1_struct_0(D_580),u1_struct_0(B_582))
      | ~ v1_funct_1(E_584)
      | ~ m1_pre_topc(D_580,A_586)
      | v2_struct_0(D_580)
      | ~ m1_pre_topc(C_581,A_586)
      | v2_struct_0(C_581)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ l1_pre_topc(A_586)
      | ~ v2_pre_topc(A_586)
      | v2_struct_0(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_309,plain,(
    ! [F_585] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_585,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_585)
      | ~ v3_pre_topc(F_585,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_585,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_200,c_305])).

tff(c_316,plain,(
    ! [F_585] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_585,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_585)
      | ~ v3_pre_topc(F_585,'#skF_4')
      | ~ m1_subset_1(F_585,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_46,c_44,c_85,c_309])).

tff(c_318,plain,(
    ! [F_587] :
      ( ~ r1_tarski(F_587,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_587)
      | ~ v3_pre_topc(F_587,'#skF_4')
      | ~ m1_subset_1(F_587,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_216,c_316])).

tff(c_322,plain,(
    ! [B_22] :
      ( ~ r1_tarski(u1_struct_0(B_22),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_22))
      | ~ v3_pre_topc(u1_struct_0(B_22),'#skF_4')
      | ~ m1_pre_topc(B_22,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_318])).

tff(c_331,plain,(
    ! [B_588] :
      ( ~ r1_tarski(u1_struct_0(B_588),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_588))
      | ~ v3_pre_topc(u1_struct_0(B_588),'#skF_4')
      | ~ m1_pre_topc(B_588,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_322])).

tff(c_335,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_331])).

tff(c_338,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_335])).

tff(c_339,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_342,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_286,c_339])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_46,c_159,c_48,c_342])).

tff(c_347,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_364,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_347])).

tff(c_367,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_364])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_367])).

tff(c_370,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_464,plain,(
    ! [A_611,G_610,D_612,B_608,C_613,E_609] :
      ( r1_tmap_1(D_612,B_608,k3_tmap_1(A_611,B_608,C_613,D_612,E_609),G_610)
      | ~ r1_tmap_1(C_613,B_608,E_609,G_610)
      | ~ m1_pre_topc(D_612,C_613)
      | ~ m1_subset_1(G_610,u1_struct_0(D_612))
      | ~ m1_subset_1(G_610,u1_struct_0(C_613))
      | ~ m1_subset_1(E_609,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_613),u1_struct_0(B_608))))
      | ~ v1_funct_2(E_609,u1_struct_0(C_613),u1_struct_0(B_608))
      | ~ v1_funct_1(E_609)
      | ~ m1_pre_topc(D_612,A_611)
      | v2_struct_0(D_612)
      | ~ m1_pre_topc(C_613,A_611)
      | v2_struct_0(C_613)
      | ~ l1_pre_topc(B_608)
      | ~ v2_pre_topc(B_608)
      | v2_struct_0(B_608)
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_469,plain,(
    ! [D_612,A_611,G_610] :
      ( r1_tmap_1(D_612,'#skF_2',k3_tmap_1(A_611,'#skF_2','#skF_4',D_612,'#skF_5'),G_610)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_610)
      | ~ m1_pre_topc(D_612,'#skF_4')
      | ~ m1_subset_1(G_610,u1_struct_0(D_612))
      | ~ m1_subset_1(G_610,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_612,A_611)
      | v2_struct_0(D_612)
      | ~ m1_pre_topc('#skF_4',A_611)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_50,c_464])).

tff(c_473,plain,(
    ! [D_612,A_611,G_610] :
      ( r1_tmap_1(D_612,'#skF_2',k3_tmap_1(A_611,'#skF_2','#skF_4',D_612,'#skF_5'),G_610)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_610)
      | ~ m1_pre_topc(D_612,'#skF_4')
      | ~ m1_subset_1(G_610,u1_struct_0(D_612))
      | ~ m1_subset_1(G_610,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_612,A_611)
      | v2_struct_0(D_612)
      | ~ m1_pre_topc('#skF_4',A_611)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_469])).

tff(c_475,plain,(
    ! [D_614,A_615,G_616] :
      ( r1_tmap_1(D_614,'#skF_2',k3_tmap_1(A_615,'#skF_2','#skF_4',D_614,'#skF_5'),G_616)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_616)
      | ~ m1_pre_topc(D_614,'#skF_4')
      | ~ m1_subset_1(G_616,u1_struct_0(D_614))
      | ~ m1_subset_1(G_616,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_614,A_615)
      | v2_struct_0(D_614)
      | ~ m1_pre_topc('#skF_4',A_615)
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_473])).

tff(c_371,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_478,plain,
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
    inference(resolution,[status(thm)],[c_475,c_371])).

tff(c_481,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_44,c_85,c_46,c_370,c_478])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_481])).

tff(c_485,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_512,plain,(
    ! [A_621] :
      ( ~ v1_xboole_0(u1_struct_0(A_621))
      | ~ l1_struct_0(A_621)
      | v2_struct_0(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_515,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_485,c_512])).

tff(c_518,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_515])).

tff(c_521,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_518])).

tff(c_525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:25:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  
% 3.33/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.48  
% 3.33/1.48  %Foreground sorts:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Background operators:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Foreground operators:
% 3.33/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.48  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.33/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.33/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.48  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.33/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.48  
% 3.54/1.50  tff(f_265, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.54/1.50  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.54/1.50  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.50  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.54/1.50  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.54/1.50  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.54/1.50  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.54/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.50  tff(f_214, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.54/1.50  tff(f_157, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.54/1.50  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.54/1.50  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_492, plain, (![B_619, A_620]: (l1_pre_topc(B_619) | ~m1_pre_topc(B_619, A_620) | ~l1_pre_topc(A_620))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.50  tff(c_498, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_492])).
% 3.54/1.50  tff(c_507, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_498])).
% 3.54/1.50  tff(c_18, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.50  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_85, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.54/1.50  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_93, plain, (![B_534, A_535]: (v1_xboole_0(B_534) | ~m1_subset_1(B_534, A_535) | ~v1_xboole_0(A_535))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.54/1.50  tff(c_104, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_85, c_93])).
% 3.54/1.50  tff(c_106, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_104])).
% 3.54/1.50  tff(c_10, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.54/1.50  tff(c_114, plain, (![B_539, A_540]: (l1_pre_topc(B_539) | ~m1_pre_topc(B_539, A_540) | ~l1_pre_topc(A_540))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.50  tff(c_117, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_114])).
% 3.54/1.50  tff(c_126, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_117])).
% 3.54/1.50  tff(c_147, plain, (![B_547, A_548]: (v2_pre_topc(B_547) | ~m1_pre_topc(B_547, A_548) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.50  tff(c_150, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_147])).
% 3.54/1.50  tff(c_159, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_150])).
% 3.54/1.50  tff(c_48, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_30, plain, (![B_22, A_20]: (m1_subset_1(u1_struct_0(B_22), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.54/1.50  tff(c_279, plain, (![B_567, A_568]: (v3_pre_topc(u1_struct_0(B_567), A_568) | ~v1_tsep_1(B_567, A_568) | ~m1_subset_1(u1_struct_0(B_567), k1_zfmisc_1(u1_struct_0(A_568))) | ~m1_pre_topc(B_567, A_568) | ~l1_pre_topc(A_568) | ~v2_pre_topc(A_568))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.54/1.50  tff(c_286, plain, (![B_22, A_20]: (v3_pre_topc(u1_struct_0(B_22), A_20) | ~v1_tsep_1(B_22, A_20) | ~v2_pre_topc(A_20) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_30, c_279])).
% 3.54/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.50  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 3.54/1.50  tff(c_200, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_83])).
% 3.54/1.50  tff(c_76, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_84, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 3.54/1.50  tff(c_216, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_84])).
% 3.54/1.50  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_265])).
% 3.54/1.50  tff(c_305, plain, (![H_583, F_585, A_586, D_580, C_581, B_582, E_584]: (r1_tmap_1(D_580, B_582, E_584, H_583) | ~r1_tmap_1(C_581, B_582, k3_tmap_1(A_586, B_582, D_580, C_581, E_584), H_583) | ~r1_tarski(F_585, u1_struct_0(C_581)) | ~r2_hidden(H_583, F_585) | ~v3_pre_topc(F_585, D_580) | ~m1_subset_1(H_583, u1_struct_0(C_581)) | ~m1_subset_1(H_583, u1_struct_0(D_580)) | ~m1_subset_1(F_585, k1_zfmisc_1(u1_struct_0(D_580))) | ~m1_pre_topc(C_581, D_580) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_580), u1_struct_0(B_582)))) | ~v1_funct_2(E_584, u1_struct_0(D_580), u1_struct_0(B_582)) | ~v1_funct_1(E_584) | ~m1_pre_topc(D_580, A_586) | v2_struct_0(D_580) | ~m1_pre_topc(C_581, A_586) | v2_struct_0(C_581) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~l1_pre_topc(A_586) | ~v2_pre_topc(A_586) | v2_struct_0(A_586))), inference(cnfTransformation, [status(thm)], [f_214])).
% 3.54/1.50  tff(c_309, plain, (![F_585]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_585, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_585) | ~v3_pre_topc(F_585, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_585, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_200, c_305])).
% 3.54/1.50  tff(c_316, plain, (![F_585]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_585, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_585) | ~v3_pre_topc(F_585, '#skF_4') | ~m1_subset_1(F_585, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_46, c_44, c_85, c_309])).
% 3.54/1.50  tff(c_318, plain, (![F_587]: (~r1_tarski(F_587, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_587) | ~v3_pre_topc(F_587, '#skF_4') | ~m1_subset_1(F_587, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_216, c_316])).
% 3.54/1.50  tff(c_322, plain, (![B_22]: (~r1_tarski(u1_struct_0(B_22), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_22)) | ~v3_pre_topc(u1_struct_0(B_22), '#skF_4') | ~m1_pre_topc(B_22, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_318])).
% 3.54/1.50  tff(c_331, plain, (![B_588]: (~r1_tarski(u1_struct_0(B_588), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_588)) | ~v3_pre_topc(u1_struct_0(B_588), '#skF_4') | ~m1_pre_topc(B_588, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_322])).
% 3.54/1.50  tff(c_335, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_331])).
% 3.54/1.50  tff(c_338, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_335])).
% 3.54/1.50  tff(c_339, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_338])).
% 3.54/1.50  tff(c_342, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_286, c_339])).
% 3.54/1.50  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_46, c_159, c_48, c_342])).
% 3.54/1.50  tff(c_347, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_338])).
% 3.54/1.50  tff(c_364, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_347])).
% 3.54/1.50  tff(c_367, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_364])).
% 3.54/1.50  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_367])).
% 3.54/1.50  tff(c_370, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 3.54/1.50  tff(c_464, plain, (![A_611, G_610, D_612, B_608, C_613, E_609]: (r1_tmap_1(D_612, B_608, k3_tmap_1(A_611, B_608, C_613, D_612, E_609), G_610) | ~r1_tmap_1(C_613, B_608, E_609, G_610) | ~m1_pre_topc(D_612, C_613) | ~m1_subset_1(G_610, u1_struct_0(D_612)) | ~m1_subset_1(G_610, u1_struct_0(C_613)) | ~m1_subset_1(E_609, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_613), u1_struct_0(B_608)))) | ~v1_funct_2(E_609, u1_struct_0(C_613), u1_struct_0(B_608)) | ~v1_funct_1(E_609) | ~m1_pre_topc(D_612, A_611) | v2_struct_0(D_612) | ~m1_pre_topc(C_613, A_611) | v2_struct_0(C_613) | ~l1_pre_topc(B_608) | ~v2_pre_topc(B_608) | v2_struct_0(B_608) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.54/1.50  tff(c_469, plain, (![D_612, A_611, G_610]: (r1_tmap_1(D_612, '#skF_2', k3_tmap_1(A_611, '#skF_2', '#skF_4', D_612, '#skF_5'), G_610) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_610) | ~m1_pre_topc(D_612, '#skF_4') | ~m1_subset_1(G_610, u1_struct_0(D_612)) | ~m1_subset_1(G_610, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_612, A_611) | v2_struct_0(D_612) | ~m1_pre_topc('#skF_4', A_611) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(resolution, [status(thm)], [c_50, c_464])).
% 3.54/1.50  tff(c_473, plain, (![D_612, A_611, G_610]: (r1_tmap_1(D_612, '#skF_2', k3_tmap_1(A_611, '#skF_2', '#skF_4', D_612, '#skF_5'), G_610) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_610) | ~m1_pre_topc(D_612, '#skF_4') | ~m1_subset_1(G_610, u1_struct_0(D_612)) | ~m1_subset_1(G_610, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_612, A_611) | v2_struct_0(D_612) | ~m1_pre_topc('#skF_4', A_611) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_469])).
% 3.54/1.50  tff(c_475, plain, (![D_614, A_615, G_616]: (r1_tmap_1(D_614, '#skF_2', k3_tmap_1(A_615, '#skF_2', '#skF_4', D_614, '#skF_5'), G_616) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_616) | ~m1_pre_topc(D_614, '#skF_4') | ~m1_subset_1(G_616, u1_struct_0(D_614)) | ~m1_subset_1(G_616, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_614, A_615) | v2_struct_0(D_614) | ~m1_pre_topc('#skF_4', A_615) | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_473])).
% 3.54/1.50  tff(c_371, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 3.54/1.50  tff(c_478, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_475, c_371])).
% 3.54/1.50  tff(c_481, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_44, c_85, c_46, c_370, c_478])).
% 3.54/1.50  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_481])).
% 3.54/1.50  tff(c_485, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_104])).
% 3.54/1.50  tff(c_512, plain, (![A_621]: (~v1_xboole_0(u1_struct_0(A_621)) | ~l1_struct_0(A_621) | v2_struct_0(A_621))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.50  tff(c_515, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_485, c_512])).
% 3.54/1.50  tff(c_518, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_515])).
% 3.54/1.50  tff(c_521, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_518])).
% 3.54/1.50  tff(c_525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_507, c_521])).
% 3.54/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.50  
% 3.54/1.50  Inference rules
% 3.54/1.50  ----------------------
% 3.54/1.50  #Ref     : 0
% 3.54/1.50  #Sup     : 77
% 3.54/1.50  #Fact    : 0
% 3.54/1.50  #Define  : 0
% 3.54/1.50  #Split   : 6
% 3.54/1.50  #Chain   : 0
% 3.54/1.50  #Close   : 0
% 3.54/1.50  
% 3.54/1.50  Ordering : KBO
% 3.54/1.50  
% 3.54/1.50  Simplification rules
% 3.54/1.50  ----------------------
% 3.54/1.50  #Subsume      : 19
% 3.54/1.50  #Demod        : 153
% 3.54/1.50  #Tautology    : 36
% 3.54/1.50  #SimpNegUnit  : 8
% 3.54/1.50  #BackRed      : 0
% 3.54/1.50  
% 3.54/1.50  #Partial instantiations: 0
% 3.54/1.50  #Strategies tried      : 1
% 3.54/1.50  
% 3.54/1.50  Timing (in seconds)
% 3.54/1.50  ----------------------
% 3.54/1.51  Preprocessing        : 0.41
% 3.54/1.51  Parsing              : 0.20
% 3.54/1.51  CNF conversion       : 0.06
% 3.54/1.51  Main loop            : 0.31
% 3.54/1.51  Inferencing          : 0.10
% 3.54/1.51  Reduction            : 0.10
% 3.54/1.51  Demodulation         : 0.08
% 3.54/1.51  BG Simplification    : 0.02
% 3.54/1.51  Subsumption          : 0.06
% 3.54/1.51  Abstraction          : 0.01
% 3.54/1.51  MUC search           : 0.00
% 3.54/1.51  Cooper               : 0.00
% 3.54/1.51  Total                : 0.76
% 3.54/1.51  Index Insertion      : 0.00
% 3.54/1.51  Index Deletion       : 0.00
% 3.54/1.51  Index Matching       : 0.00
% 3.54/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
