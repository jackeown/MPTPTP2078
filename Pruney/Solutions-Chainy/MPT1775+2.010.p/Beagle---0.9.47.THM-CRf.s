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
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 266 expanded)
%              Number of leaves         :   40 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          :  362 (1862 expanded)
%              Number of equality atoms :    5 (  85 expanded)
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

tff(f_270,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_219,axiom,(
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

tff(f_162,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_583,plain,(
    ! [B_633,A_634] :
      ( l1_pre_topc(B_633)
      | ~ m1_pre_topc(B_633,A_634)
      | ~ l1_pre_topc(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_592,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_583])).

tff(c_602,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_592])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_38,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_110,plain,(
    ! [B_540,A_541] :
      ( l1_pre_topc(B_540)
      | ~ m1_pre_topc(B_540,A_541)
      | ~ l1_pre_topc(A_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_110])).

tff(c_129,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_119])).

tff(c_26,plain,(
    ! [A_21] :
      ( m1_pre_topc(A_21,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_90,plain,(
    ! [B_536,A_537] :
      ( v1_xboole_0(B_536)
      | ~ m1_subset_1(B_536,A_537)
      | ~ v1_xboole_0(A_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_101,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_90])).

tff(c_103,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_46,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_110])).

tff(c_126,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_116])).

tff(c_140,plain,(
    ! [B_547,A_548] :
      ( v2_pre_topc(B_547)
      | ~ m1_pre_topc(B_547,A_548)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_140])).

tff(c_156,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_146])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_282,plain,(
    ! [B_565,A_566] :
      ( v3_pre_topc(u1_struct_0(B_565),A_566)
      | ~ v1_tsep_1(B_565,A_566)
      | ~ m1_subset_1(u1_struct_0(B_565),k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ m1_pre_topc(B_565,A_566)
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_289,plain,(
    ! [B_20,A_18] :
      ( v3_pre_topc(u1_struct_0(B_20),A_18)
      | ~ v1_tsep_1(B_20,A_18)
      | ~ v2_pre_topc(A_18)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_282])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( r1_tarski(u1_struct_0(B_24),u1_struct_0(A_22))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_167,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_81,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_187,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_81])).

tff(c_318,plain,(
    ! [B_585,H_582,D_583,C_587,A_586,F_588,E_584] :
      ( r1_tmap_1(D_583,B_585,E_584,H_582)
      | ~ r1_tmap_1(C_587,B_585,k3_tmap_1(A_586,B_585,D_583,C_587,E_584),H_582)
      | ~ r1_tarski(F_588,u1_struct_0(C_587))
      | ~ r2_hidden(H_582,F_588)
      | ~ v3_pre_topc(F_588,D_583)
      | ~ m1_subset_1(H_582,u1_struct_0(C_587))
      | ~ m1_subset_1(H_582,u1_struct_0(D_583))
      | ~ m1_subset_1(F_588,k1_zfmisc_1(u1_struct_0(D_583)))
      | ~ m1_pre_topc(C_587,D_583)
      | ~ m1_subset_1(E_584,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583),u1_struct_0(B_585))))
      | ~ v1_funct_2(E_584,u1_struct_0(D_583),u1_struct_0(B_585))
      | ~ v1_funct_1(E_584)
      | ~ m1_pre_topc(D_583,A_586)
      | v2_struct_0(D_583)
      | ~ m1_pre_topc(C_587,A_586)
      | v2_struct_0(C_587)
      | ~ l1_pre_topc(B_585)
      | ~ v2_pre_topc(B_585)
      | v2_struct_0(B_585)
      | ~ l1_pre_topc(A_586)
      | ~ v2_pre_topc(A_586)
      | v2_struct_0(A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_322,plain,(
    ! [F_588] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_588,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_588)
      | ~ v3_pre_topc(F_588,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_588,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_187,c_318])).

tff(c_329,plain,(
    ! [F_588] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_588,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_588)
      | ~ v3_pre_topc(F_588,'#skF_4')
      | ~ m1_subset_1(F_588,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_50,c_48,c_44,c_42,c_83,c_322])).

tff(c_331,plain,(
    ! [F_589] :
      ( ~ r1_tarski(F_589,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_589)
      | ~ v3_pre_topc(F_589,'#skF_4')
      | ~ m1_subset_1(F_589,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_167,c_329])).

tff(c_335,plain,(
    ! [B_20] :
      ( ~ r1_tarski(u1_struct_0(B_20),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_20))
      | ~ v3_pre_topc(u1_struct_0(B_20),'#skF_4')
      | ~ m1_pre_topc(B_20,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_331])).

tff(c_344,plain,(
    ! [B_590] :
      ( ~ r1_tarski(u1_struct_0(B_590),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_590))
      | ~ v3_pre_topc(u1_struct_0(B_590),'#skF_4')
      | ~ m1_pre_topc(B_590,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_335])).

tff(c_348,plain,(
    ! [B_24] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_24))
      | ~ v3_pre_topc(u1_struct_0(B_24),'#skF_4')
      | ~ m1_pre_topc(B_24,'#skF_4')
      | ~ m1_pre_topc(B_24,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_352,plain,(
    ! [B_591] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_591))
      | ~ v3_pre_topc(u1_struct_0(B_591),'#skF_4')
      | ~ m1_pre_topc(B_591,'#skF_4')
      | ~ m1_pre_topc(B_591,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_348])).

tff(c_356,plain,(
    ! [B_20] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_20))
      | ~ m1_pre_topc(B_20,'#skF_3')
      | ~ v1_tsep_1(B_20,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_20,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_289,c_352])).

tff(c_360,plain,(
    ! [B_592] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_592))
      | ~ m1_pre_topc(B_592,'#skF_3')
      | ~ v1_tsep_1(B_592,'#skF_4')
      | ~ m1_pre_topc(B_592,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_156,c_356])).

tff(c_373,plain,(
    ! [B_599] :
      ( ~ m1_pre_topc(B_599,'#skF_3')
      | ~ v1_tsep_1(B_599,'#skF_4')
      | ~ m1_pre_topc(B_599,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_599))
      | v1_xboole_0(u1_struct_0(B_599)) ) ),
    inference(resolution,[status(thm)],[c_4,c_360])).

tff(c_379,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_373])).

tff(c_386,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_379])).

tff(c_387,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_386])).

tff(c_399,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_387])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_399])).

tff(c_411,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_554,plain,(
    ! [D_623,E_622,B_626,G_625,C_627,A_624] :
      ( r1_tmap_1(D_623,B_626,k3_tmap_1(A_624,B_626,C_627,D_623,E_622),G_625)
      | ~ r1_tmap_1(C_627,B_626,E_622,G_625)
      | ~ m1_pre_topc(D_623,C_627)
      | ~ m1_subset_1(G_625,u1_struct_0(D_623))
      | ~ m1_subset_1(G_625,u1_struct_0(C_627))
      | ~ m1_subset_1(E_622,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627),u1_struct_0(B_626))))
      | ~ v1_funct_2(E_622,u1_struct_0(C_627),u1_struct_0(B_626))
      | ~ v1_funct_1(E_622)
      | ~ m1_pre_topc(D_623,A_624)
      | v2_struct_0(D_623)
      | ~ m1_pre_topc(C_627,A_624)
      | v2_struct_0(C_627)
      | ~ l1_pre_topc(B_626)
      | ~ v2_pre_topc(B_626)
      | v2_struct_0(B_626)
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_559,plain,(
    ! [D_623,A_624,G_625] :
      ( r1_tmap_1(D_623,'#skF_2',k3_tmap_1(A_624,'#skF_2','#skF_4',D_623,'#skF_5'),G_625)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_625)
      | ~ m1_pre_topc(D_623,'#skF_4')
      | ~ m1_subset_1(G_625,u1_struct_0(D_623))
      | ~ m1_subset_1(G_625,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_623,A_624)
      | v2_struct_0(D_623)
      | ~ m1_pre_topc('#skF_4',A_624)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(resolution,[status(thm)],[c_48,c_554])).

tff(c_563,plain,(
    ! [D_623,A_624,G_625] :
      ( r1_tmap_1(D_623,'#skF_2',k3_tmap_1(A_624,'#skF_2','#skF_4',D_623,'#skF_5'),G_625)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_625)
      | ~ m1_pre_topc(D_623,'#skF_4')
      | ~ m1_subset_1(G_625,u1_struct_0(D_623))
      | ~ m1_subset_1(G_625,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_623,A_624)
      | v2_struct_0(D_623)
      | ~ m1_pre_topc('#skF_4',A_624)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_624)
      | ~ v2_pre_topc(A_624)
      | v2_struct_0(A_624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_50,c_559])).

tff(c_565,plain,(
    ! [D_628,A_629,G_630] :
      ( r1_tmap_1(D_628,'#skF_2',k3_tmap_1(A_629,'#skF_2','#skF_4',D_628,'#skF_5'),G_630)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_630)
      | ~ m1_pre_topc(D_628,'#skF_4')
      | ~ m1_subset_1(G_630,u1_struct_0(D_628))
      | ~ m1_subset_1(G_630,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_628,A_629)
      | v2_struct_0(D_628)
      | ~ m1_pre_topc('#skF_4',A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_56,c_563])).

tff(c_410,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_412,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_412])).

tff(c_415,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_568,plain,
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
    inference(resolution,[status(thm)],[c_565,c_415])).

tff(c_571,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_58,c_42,c_83,c_44,c_411,c_568])).

tff(c_573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_571])).

tff(c_575,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_606,plain,(
    ! [A_635] :
      ( ~ v1_xboole_0(u1_struct_0(A_635))
      | ~ l1_struct_0(A_635)
      | v2_struct_0(A_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_609,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_575,c_606])).

tff(c_612,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_609])).

tff(c_616,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_612])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_616])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:06:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.56  
% 3.44/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.56  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.44/1.56  
% 3.44/1.56  %Foreground sorts:
% 3.44/1.56  
% 3.44/1.56  
% 3.44/1.56  %Background operators:
% 3.44/1.56  
% 3.44/1.56  
% 3.44/1.56  %Foreground operators:
% 3.44/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.44/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.44/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.44/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.44/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.44/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.44/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.56  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.44/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.44/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.44/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.44/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.56  
% 3.44/1.58  tff(f_270, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.44/1.58  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.44/1.58  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.44/1.58  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.44/1.58  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.44/1.58  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.44/1.58  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.44/1.58  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.44/1.58  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.44/1.58  tff(f_219, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.44/1.58  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.44/1.58  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.44/1.58  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_583, plain, (![B_633, A_634]: (l1_pre_topc(B_633) | ~m1_pre_topc(B_633, A_634) | ~l1_pre_topc(A_634))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.58  tff(c_592, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_583])).
% 3.44/1.58  tff(c_602, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_592])).
% 3.44/1.58  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.58  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_38, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.44/1.58  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_110, plain, (![B_540, A_541]: (l1_pre_topc(B_540) | ~m1_pre_topc(B_540, A_541) | ~l1_pre_topc(A_541))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.58  tff(c_119, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_110])).
% 3.44/1.58  tff(c_129, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_119])).
% 3.44/1.58  tff(c_26, plain, (![A_21]: (m1_pre_topc(A_21, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.44/1.58  tff(c_90, plain, (![B_536, A_537]: (v1_xboole_0(B_536) | ~m1_subset_1(B_536, A_537) | ~v1_xboole_0(A_537))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.58  tff(c_101, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_90])).
% 3.44/1.58  tff(c_103, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_101])).
% 3.44/1.58  tff(c_46, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.58  tff(c_116, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_110])).
% 3.44/1.58  tff(c_126, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_116])).
% 3.44/1.58  tff(c_140, plain, (![B_547, A_548]: (v2_pre_topc(B_547) | ~m1_pre_topc(B_547, A_548) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.58  tff(c_146, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_140])).
% 3.44/1.58  tff(c_156, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_146])).
% 3.44/1.58  tff(c_24, plain, (![B_20, A_18]: (m1_subset_1(u1_struct_0(B_20), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.44/1.58  tff(c_282, plain, (![B_565, A_566]: (v3_pre_topc(u1_struct_0(B_565), A_566) | ~v1_tsep_1(B_565, A_566) | ~m1_subset_1(u1_struct_0(B_565), k1_zfmisc_1(u1_struct_0(A_566))) | ~m1_pre_topc(B_565, A_566) | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.58  tff(c_289, plain, (![B_20, A_18]: (v3_pre_topc(u1_struct_0(B_20), A_18) | ~v1_tsep_1(B_20, A_18) | ~v2_pre_topc(A_18) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_24, c_282])).
% 3.44/1.58  tff(c_28, plain, (![B_24, A_22]: (r1_tarski(u1_struct_0(B_24), u1_struct_0(A_22)) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.44/1.58  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_82, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74])).
% 3.44/1.58  tff(c_167, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_82])).
% 3.44/1.58  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_270])).
% 3.44/1.58  tff(c_81, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 3.44/1.58  tff(c_187, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_167, c_81])).
% 3.44/1.58  tff(c_318, plain, (![B_585, H_582, D_583, C_587, A_586, F_588, E_584]: (r1_tmap_1(D_583, B_585, E_584, H_582) | ~r1_tmap_1(C_587, B_585, k3_tmap_1(A_586, B_585, D_583, C_587, E_584), H_582) | ~r1_tarski(F_588, u1_struct_0(C_587)) | ~r2_hidden(H_582, F_588) | ~v3_pre_topc(F_588, D_583) | ~m1_subset_1(H_582, u1_struct_0(C_587)) | ~m1_subset_1(H_582, u1_struct_0(D_583)) | ~m1_subset_1(F_588, k1_zfmisc_1(u1_struct_0(D_583))) | ~m1_pre_topc(C_587, D_583) | ~m1_subset_1(E_584, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583), u1_struct_0(B_585)))) | ~v1_funct_2(E_584, u1_struct_0(D_583), u1_struct_0(B_585)) | ~v1_funct_1(E_584) | ~m1_pre_topc(D_583, A_586) | v2_struct_0(D_583) | ~m1_pre_topc(C_587, A_586) | v2_struct_0(C_587) | ~l1_pre_topc(B_585) | ~v2_pre_topc(B_585) | v2_struct_0(B_585) | ~l1_pre_topc(A_586) | ~v2_pre_topc(A_586) | v2_struct_0(A_586))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.44/1.58  tff(c_322, plain, (![F_588]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_588, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_588) | ~v3_pre_topc(F_588, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_588, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_187, c_318])).
% 3.44/1.58  tff(c_329, plain, (![F_588]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_588, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_588) | ~v3_pre_topc(F_588, '#skF_4') | ~m1_subset_1(F_588, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_50, c_48, c_44, c_42, c_83, c_322])).
% 3.44/1.58  tff(c_331, plain, (![F_589]: (~r1_tarski(F_589, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_589) | ~v3_pre_topc(F_589, '#skF_4') | ~m1_subset_1(F_589, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_167, c_329])).
% 3.44/1.58  tff(c_335, plain, (![B_20]: (~r1_tarski(u1_struct_0(B_20), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_20)) | ~v3_pre_topc(u1_struct_0(B_20), '#skF_4') | ~m1_pre_topc(B_20, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_331])).
% 3.44/1.58  tff(c_344, plain, (![B_590]: (~r1_tarski(u1_struct_0(B_590), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_590)) | ~v3_pre_topc(u1_struct_0(B_590), '#skF_4') | ~m1_pre_topc(B_590, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_335])).
% 3.44/1.58  tff(c_348, plain, (![B_24]: (~r2_hidden('#skF_6', u1_struct_0(B_24)) | ~v3_pre_topc(u1_struct_0(B_24), '#skF_4') | ~m1_pre_topc(B_24, '#skF_4') | ~m1_pre_topc(B_24, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_344])).
% 3.44/1.58  tff(c_352, plain, (![B_591]: (~r2_hidden('#skF_6', u1_struct_0(B_591)) | ~v3_pre_topc(u1_struct_0(B_591), '#skF_4') | ~m1_pre_topc(B_591, '#skF_4') | ~m1_pre_topc(B_591, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_348])).
% 3.44/1.58  tff(c_356, plain, (![B_20]: (~r2_hidden('#skF_6', u1_struct_0(B_20)) | ~m1_pre_topc(B_20, '#skF_3') | ~v1_tsep_1(B_20, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_20, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_289, c_352])).
% 3.44/1.58  tff(c_360, plain, (![B_592]: (~r2_hidden('#skF_6', u1_struct_0(B_592)) | ~m1_pre_topc(B_592, '#skF_3') | ~v1_tsep_1(B_592, '#skF_4') | ~m1_pre_topc(B_592, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_156, c_356])).
% 3.44/1.58  tff(c_373, plain, (![B_599]: (~m1_pre_topc(B_599, '#skF_3') | ~v1_tsep_1(B_599, '#skF_4') | ~m1_pre_topc(B_599, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0(B_599)) | v1_xboole_0(u1_struct_0(B_599)))), inference(resolution, [status(thm)], [c_4, c_360])).
% 3.44/1.58  tff(c_379, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_373])).
% 3.44/1.58  tff(c_386, plain, (~m1_pre_topc('#skF_3', '#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_379])).
% 3.44/1.58  tff(c_387, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_103, c_386])).
% 3.44/1.58  tff(c_399, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_387])).
% 3.44/1.58  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_399])).
% 3.44/1.58  tff(c_411, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 3.44/1.58  tff(c_554, plain, (![D_623, E_622, B_626, G_625, C_627, A_624]: (r1_tmap_1(D_623, B_626, k3_tmap_1(A_624, B_626, C_627, D_623, E_622), G_625) | ~r1_tmap_1(C_627, B_626, E_622, G_625) | ~m1_pre_topc(D_623, C_627) | ~m1_subset_1(G_625, u1_struct_0(D_623)) | ~m1_subset_1(G_625, u1_struct_0(C_627)) | ~m1_subset_1(E_622, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627), u1_struct_0(B_626)))) | ~v1_funct_2(E_622, u1_struct_0(C_627), u1_struct_0(B_626)) | ~v1_funct_1(E_622) | ~m1_pre_topc(D_623, A_624) | v2_struct_0(D_623) | ~m1_pre_topc(C_627, A_624) | v2_struct_0(C_627) | ~l1_pre_topc(B_626) | ~v2_pre_topc(B_626) | v2_struct_0(B_626) | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.44/1.58  tff(c_559, plain, (![D_623, A_624, G_625]: (r1_tmap_1(D_623, '#skF_2', k3_tmap_1(A_624, '#skF_2', '#skF_4', D_623, '#skF_5'), G_625) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_625) | ~m1_pre_topc(D_623, '#skF_4') | ~m1_subset_1(G_625, u1_struct_0(D_623)) | ~m1_subset_1(G_625, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_623, A_624) | v2_struct_0(D_623) | ~m1_pre_topc('#skF_4', A_624) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(resolution, [status(thm)], [c_48, c_554])).
% 3.44/1.58  tff(c_563, plain, (![D_623, A_624, G_625]: (r1_tmap_1(D_623, '#skF_2', k3_tmap_1(A_624, '#skF_2', '#skF_4', D_623, '#skF_5'), G_625) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_625) | ~m1_pre_topc(D_623, '#skF_4') | ~m1_subset_1(G_625, u1_struct_0(D_623)) | ~m1_subset_1(G_625, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_623, A_624) | v2_struct_0(D_623) | ~m1_pre_topc('#skF_4', A_624) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_624) | ~v2_pre_topc(A_624) | v2_struct_0(A_624))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_50, c_559])).
% 3.44/1.58  tff(c_565, plain, (![D_628, A_629, G_630]: (r1_tmap_1(D_628, '#skF_2', k3_tmap_1(A_629, '#skF_2', '#skF_4', D_628, '#skF_5'), G_630) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_630) | ~m1_pre_topc(D_628, '#skF_4') | ~m1_subset_1(G_630, u1_struct_0(D_628)) | ~m1_subset_1(G_630, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_628, A_629) | v2_struct_0(D_628) | ~m1_pre_topc('#skF_4', A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(negUnitSimplification, [status(thm)], [c_66, c_56, c_563])).
% 3.44/1.58  tff(c_410, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 3.44/1.58  tff(c_412, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_81])).
% 3.44/1.58  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_412])).
% 3.44/1.58  tff(c_415, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 3.44/1.58  tff(c_568, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_565, c_415])).
% 3.44/1.58  tff(c_571, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_58, c_42, c_83, c_44, c_411, c_568])).
% 3.44/1.58  tff(c_573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_571])).
% 3.44/1.58  tff(c_575, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_101])).
% 3.44/1.58  tff(c_606, plain, (![A_635]: (~v1_xboole_0(u1_struct_0(A_635)) | ~l1_struct_0(A_635) | v2_struct_0(A_635))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.58  tff(c_609, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_575, c_606])).
% 3.44/1.58  tff(c_612, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_609])).
% 3.44/1.58  tff(c_616, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_612])).
% 3.44/1.58  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_602, c_616])).
% 3.44/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  Inference rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Ref     : 0
% 3.44/1.58  #Sup     : 99
% 3.44/1.58  #Fact    : 0
% 3.44/1.58  #Define  : 0
% 3.44/1.58  #Split   : 7
% 3.44/1.58  #Chain   : 0
% 3.44/1.58  #Close   : 0
% 3.44/1.58  
% 3.44/1.58  Ordering : KBO
% 3.44/1.58  
% 3.44/1.58  Simplification rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Subsume      : 23
% 3.44/1.58  #Demod        : 158
% 3.44/1.58  #Tautology    : 44
% 3.44/1.58  #SimpNegUnit  : 11
% 3.44/1.58  #BackRed      : 0
% 3.44/1.58  
% 3.44/1.58  #Partial instantiations: 0
% 3.44/1.58  #Strategies tried      : 1
% 3.44/1.58  
% 3.44/1.58  Timing (in seconds)
% 3.44/1.58  ----------------------
% 3.44/1.59  Preprocessing        : 0.43
% 3.44/1.59  Parsing              : 0.22
% 3.44/1.59  CNF conversion       : 0.07
% 3.44/1.59  Main loop            : 0.35
% 3.44/1.59  Inferencing          : 0.12
% 3.44/1.59  Reduction            : 0.11
% 3.44/1.59  Demodulation         : 0.08
% 3.44/1.59  BG Simplification    : 0.02
% 3.44/1.59  Subsumption          : 0.08
% 3.44/1.59  Abstraction          : 0.01
% 3.44/1.59  MUC search           : 0.00
% 3.44/1.59  Cooper               : 0.00
% 3.44/1.59  Total                : 0.82
% 3.44/1.59  Index Insertion      : 0.00
% 3.44/1.59  Index Deletion       : 0.00
% 3.44/1.59  Index Matching       : 0.00
% 3.44/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
