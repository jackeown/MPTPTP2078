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
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 299 expanded)
%              Number of leaves         :   39 ( 132 expanded)
%              Depth                    :   17
%              Number of atoms          :  319 (2268 expanded)
%              Number of equality atoms :    6 ( 106 expanded)
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

tff(f_258,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_83,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_150,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_34,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_88,plain,(
    ! [B_535,A_536] :
      ( l1_pre_topc(B_535)
      | ~ m1_pre_topc(B_535,A_536)
      | ~ l1_pre_topc(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_100,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_91])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_103,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94])).

tff(c_115,plain,(
    ! [B_541,A_542] :
      ( v2_pre_topc(B_541)
      | ~ m1_pre_topc(B_541,A_542)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_130,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_121])).

tff(c_42,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_231,plain,(
    ! [B_555,A_556] :
      ( v3_pre_topc(u1_struct_0(B_555),A_556)
      | ~ v1_tsep_1(B_555,A_556)
      | ~ m1_subset_1(u1_struct_0(B_555),k1_zfmisc_1(u1_struct_0(A_556)))
      | ~ m1_pre_topc(B_555,A_556)
      | ~ l1_pre_topc(A_556)
      | ~ v2_pre_topc(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ! [B_22,A_20] :
      ( v3_pre_topc(u1_struct_0(B_22),A_20)
      | ~ v1_tsep_1(B_22,A_20)
      | ~ v2_pre_topc(A_20)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_231])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_134,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_149,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_78])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_255,plain,(
    ! [E_576,B_574,C_573,D_572,A_578,H_575,F_577] :
      ( r1_tmap_1(D_572,B_574,E_576,H_575)
      | ~ r1_tmap_1(C_573,B_574,k3_tmap_1(A_578,B_574,D_572,C_573,E_576),H_575)
      | ~ r1_tarski(F_577,u1_struct_0(C_573))
      | ~ r2_hidden(H_575,F_577)
      | ~ v3_pre_topc(F_577,D_572)
      | ~ m1_subset_1(H_575,u1_struct_0(C_573))
      | ~ m1_subset_1(H_575,u1_struct_0(D_572))
      | ~ m1_subset_1(F_577,k1_zfmisc_1(u1_struct_0(D_572)))
      | ~ m1_pre_topc(C_573,D_572)
      | ~ m1_subset_1(E_576,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_572),u1_struct_0(B_574))))
      | ~ v1_funct_2(E_576,u1_struct_0(D_572),u1_struct_0(B_574))
      | ~ v1_funct_1(E_576)
      | ~ m1_pre_topc(D_572,A_578)
      | v2_struct_0(D_572)
      | ~ m1_pre_topc(C_573,A_578)
      | v2_struct_0(C_573)
      | ~ l1_pre_topc(B_574)
      | ~ v2_pre_topc(B_574)
      | v2_struct_0(B_574)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_259,plain,(
    ! [F_577] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_577,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_577)
      | ~ v3_pre_topc(F_577,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_577,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_134,c_255])).

tff(c_266,plain,(
    ! [F_577] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_577,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_577)
      | ~ v3_pre_topc(F_577,'#skF_4')
      | ~ m1_subset_1(F_577,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_54,c_50,c_48,c_46,c_44,c_40,c_38,c_79,c_259])).

tff(c_268,plain,(
    ! [F_579] :
      ( ~ r1_tarski(F_579,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_579)
      | ~ v3_pre_topc(F_579,'#skF_4')
      | ~ m1_subset_1(F_579,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_56,c_52,c_149,c_266])).

tff(c_272,plain,(
    ! [B_22] :
      ( ~ r1_tarski(u1_struct_0(B_22),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_22))
      | ~ v3_pre_topc(u1_struct_0(B_22),'#skF_4')
      | ~ m1_pre_topc(B_22,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_268])).

tff(c_276,plain,(
    ! [B_580] :
      ( ~ r1_tarski(u1_struct_0(B_580),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_580))
      | ~ v3_pre_topc(u1_struct_0(B_580),'#skF_4')
      | ~ m1_pre_topc(B_580,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_272])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_283,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_280])).

tff(c_284,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_287,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_235,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_40,c_130,c_42,c_287])).

tff(c_292,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_302,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_305,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_302])).

tff(c_16,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_305,c_16])).

tff(c_311,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_308])).

tff(c_314,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_314])).

tff(c_319,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_433,plain,(
    ! [B_601,C_606,D_605,E_602,A_604,G_603] :
      ( r1_tmap_1(D_605,B_601,k3_tmap_1(A_604,B_601,C_606,D_605,E_602),G_603)
      | ~ r1_tmap_1(C_606,B_601,E_602,G_603)
      | ~ m1_pre_topc(D_605,C_606)
      | ~ m1_subset_1(G_603,u1_struct_0(D_605))
      | ~ m1_subset_1(G_603,u1_struct_0(C_606))
      | ~ m1_subset_1(E_602,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_606),u1_struct_0(B_601))))
      | ~ v1_funct_2(E_602,u1_struct_0(C_606),u1_struct_0(B_601))
      | ~ v1_funct_1(E_602)
      | ~ m1_pre_topc(D_605,A_604)
      | v2_struct_0(D_605)
      | ~ m1_pre_topc(C_606,A_604)
      | v2_struct_0(C_606)
      | ~ l1_pre_topc(B_601)
      | ~ v2_pre_topc(B_601)
      | v2_struct_0(B_601)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_435,plain,(
    ! [D_605,A_604,G_603] :
      ( r1_tmap_1(D_605,'#skF_2',k3_tmap_1(A_604,'#skF_2','#skF_4',D_605,'#skF_5'),G_603)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_603)
      | ~ m1_pre_topc(D_605,'#skF_4')
      | ~ m1_subset_1(G_603,u1_struct_0(D_605))
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_605,A_604)
      | v2_struct_0(D_605)
      | ~ m1_pre_topc('#skF_4',A_604)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(resolution,[status(thm)],[c_44,c_433])).

tff(c_438,plain,(
    ! [D_605,A_604,G_603] :
      ( r1_tmap_1(D_605,'#skF_2',k3_tmap_1(A_604,'#skF_2','#skF_4',D_605,'#skF_5'),G_603)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_603)
      | ~ m1_pre_topc(D_605,'#skF_4')
      | ~ m1_subset_1(G_603,u1_struct_0(D_605))
      | ~ m1_subset_1(G_603,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_605,A_604)
      | v2_struct_0(D_605)
      | ~ m1_pre_topc('#skF_4',A_604)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_46,c_435])).

tff(c_440,plain,(
    ! [D_607,A_608,G_609] :
      ( r1_tmap_1(D_607,'#skF_2',k3_tmap_1(A_608,'#skF_2','#skF_4',D_607,'#skF_5'),G_609)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_609)
      | ~ m1_pre_topc(D_607,'#skF_4')
      | ~ m1_subset_1(G_609,u1_struct_0(D_607))
      | ~ m1_subset_1(G_609,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_607,A_608)
      | v2_struct_0(D_607)
      | ~ m1_pre_topc('#skF_4',A_608)
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_438])).

tff(c_324,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_78])).

tff(c_443,plain,
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
    inference(resolution,[status(thm)],[c_440,c_324])).

tff(c_446,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_38,c_79,c_40,c_319,c_443])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.47  
% 3.25/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.47  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.47  
% 3.25/1.47  %Foreground sorts:
% 3.25/1.47  
% 3.25/1.47  
% 3.25/1.47  %Background operators:
% 3.25/1.47  
% 3.25/1.47  
% 3.25/1.47  %Foreground operators:
% 3.25/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.47  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.25/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.25/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.47  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.25/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.25/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.25/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.47  
% 3.33/1.50  tff(f_258, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.33/1.50  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.33/1.50  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.33/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.33/1.50  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.33/1.50  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.33/1.50  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.33/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.33/1.50  tff(f_207, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.33/1.50  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.33/1.50  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.33/1.50  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_34, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.33/1.50  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_88, plain, (![B_535, A_536]: (l1_pre_topc(B_535) | ~m1_pre_topc(B_535, A_536) | ~l1_pre_topc(A_536))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.50  tff(c_91, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.33/1.50  tff(c_100, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_91])).
% 3.33/1.50  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.50  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.50  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.33/1.50  tff(c_103, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94])).
% 3.33/1.50  tff(c_115, plain, (![B_541, A_542]: (v2_pre_topc(B_541) | ~m1_pre_topc(B_541, A_542) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.50  tff(c_121, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_115])).
% 3.33/1.50  tff(c_130, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_121])).
% 3.33/1.50  tff(c_42, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_24, plain, (![B_22, A_20]: (m1_subset_1(u1_struct_0(B_22), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.33/1.50  tff(c_231, plain, (![B_555, A_556]: (v3_pre_topc(u1_struct_0(B_555), A_556) | ~v1_tsep_1(B_555, A_556) | ~m1_subset_1(u1_struct_0(B_555), k1_zfmisc_1(u1_struct_0(A_556))) | ~m1_pre_topc(B_555, A_556) | ~l1_pre_topc(A_556) | ~v2_pre_topc(A_556))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.33/1.50  tff(c_235, plain, (![B_22, A_20]: (v3_pre_topc(u1_struct_0(B_22), A_20) | ~v1_tsep_1(B_22, A_20) | ~v2_pre_topc(A_20) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_24, c_231])).
% 3.33/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.50  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 3.33/1.50  tff(c_134, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_77])).
% 3.33/1.50  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 3.33/1.50  tff(c_149, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_78])).
% 3.33/1.50  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.33/1.50  tff(c_255, plain, (![E_576, B_574, C_573, D_572, A_578, H_575, F_577]: (r1_tmap_1(D_572, B_574, E_576, H_575) | ~r1_tmap_1(C_573, B_574, k3_tmap_1(A_578, B_574, D_572, C_573, E_576), H_575) | ~r1_tarski(F_577, u1_struct_0(C_573)) | ~r2_hidden(H_575, F_577) | ~v3_pre_topc(F_577, D_572) | ~m1_subset_1(H_575, u1_struct_0(C_573)) | ~m1_subset_1(H_575, u1_struct_0(D_572)) | ~m1_subset_1(F_577, k1_zfmisc_1(u1_struct_0(D_572))) | ~m1_pre_topc(C_573, D_572) | ~m1_subset_1(E_576, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_572), u1_struct_0(B_574)))) | ~v1_funct_2(E_576, u1_struct_0(D_572), u1_struct_0(B_574)) | ~v1_funct_1(E_576) | ~m1_pre_topc(D_572, A_578) | v2_struct_0(D_572) | ~m1_pre_topc(C_573, A_578) | v2_struct_0(C_573) | ~l1_pre_topc(B_574) | ~v2_pre_topc(B_574) | v2_struct_0(B_574) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(cnfTransformation, [status(thm)], [f_207])).
% 3.33/1.50  tff(c_259, plain, (![F_577]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_577, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_577) | ~v3_pre_topc(F_577, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_577, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_134, c_255])).
% 3.33/1.50  tff(c_266, plain, (![F_577]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_577, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_577) | ~v3_pre_topc(F_577, '#skF_4') | ~m1_subset_1(F_577, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_54, c_50, c_48, c_46, c_44, c_40, c_38, c_79, c_259])).
% 3.33/1.50  tff(c_268, plain, (![F_579]: (~r1_tarski(F_579, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_579) | ~v3_pre_topc(F_579, '#skF_4') | ~m1_subset_1(F_579, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_56, c_52, c_149, c_266])).
% 3.33/1.50  tff(c_272, plain, (![B_22]: (~r1_tarski(u1_struct_0(B_22), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_22)) | ~v3_pre_topc(u1_struct_0(B_22), '#skF_4') | ~m1_pre_topc(B_22, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_268])).
% 3.33/1.50  tff(c_276, plain, (![B_580]: (~r1_tarski(u1_struct_0(B_580), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_580)) | ~v3_pre_topc(u1_struct_0(B_580), '#skF_4') | ~m1_pre_topc(B_580, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_272])).
% 3.33/1.50  tff(c_280, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_276])).
% 3.33/1.50  tff(c_283, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_280])).
% 3.33/1.50  tff(c_284, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_283])).
% 3.33/1.50  tff(c_287, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_235, c_284])).
% 3.33/1.50  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_40, c_130, c_42, c_287])).
% 3.33/1.50  tff(c_292, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_283])).
% 3.33/1.50  tff(c_302, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_292])).
% 3.33/1.50  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_302])).
% 3.33/1.50  tff(c_16, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.33/1.50  tff(c_308, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_305, c_16])).
% 3.33/1.50  tff(c_311, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_308])).
% 3.33/1.50  tff(c_314, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_311])).
% 3.33/1.50  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_314])).
% 3.33/1.50  tff(c_319, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 3.33/1.50  tff(c_433, plain, (![B_601, C_606, D_605, E_602, A_604, G_603]: (r1_tmap_1(D_605, B_601, k3_tmap_1(A_604, B_601, C_606, D_605, E_602), G_603) | ~r1_tmap_1(C_606, B_601, E_602, G_603) | ~m1_pre_topc(D_605, C_606) | ~m1_subset_1(G_603, u1_struct_0(D_605)) | ~m1_subset_1(G_603, u1_struct_0(C_606)) | ~m1_subset_1(E_602, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_606), u1_struct_0(B_601)))) | ~v1_funct_2(E_602, u1_struct_0(C_606), u1_struct_0(B_601)) | ~v1_funct_1(E_602) | ~m1_pre_topc(D_605, A_604) | v2_struct_0(D_605) | ~m1_pre_topc(C_606, A_604) | v2_struct_0(C_606) | ~l1_pre_topc(B_601) | ~v2_pre_topc(B_601) | v2_struct_0(B_601) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.33/1.50  tff(c_435, plain, (![D_605, A_604, G_603]: (r1_tmap_1(D_605, '#skF_2', k3_tmap_1(A_604, '#skF_2', '#skF_4', D_605, '#skF_5'), G_603) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_603) | ~m1_pre_topc(D_605, '#skF_4') | ~m1_subset_1(G_603, u1_struct_0(D_605)) | ~m1_subset_1(G_603, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_605, A_604) | v2_struct_0(D_605) | ~m1_pre_topc('#skF_4', A_604) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(resolution, [status(thm)], [c_44, c_433])).
% 3.33/1.50  tff(c_438, plain, (![D_605, A_604, G_603]: (r1_tmap_1(D_605, '#skF_2', k3_tmap_1(A_604, '#skF_2', '#skF_4', D_605, '#skF_5'), G_603) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_603) | ~m1_pre_topc(D_605, '#skF_4') | ~m1_subset_1(G_603, u1_struct_0(D_605)) | ~m1_subset_1(G_603, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_605, A_604) | v2_struct_0(D_605) | ~m1_pre_topc('#skF_4', A_604) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_46, c_435])).
% 3.33/1.50  tff(c_440, plain, (![D_607, A_608, G_609]: (r1_tmap_1(D_607, '#skF_2', k3_tmap_1(A_608, '#skF_2', '#skF_4', D_607, '#skF_5'), G_609) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_609) | ~m1_pre_topc(D_607, '#skF_4') | ~m1_subset_1(G_609, u1_struct_0(D_607)) | ~m1_subset_1(G_609, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_607, A_608) | v2_struct_0(D_607) | ~m1_pre_topc('#skF_4', A_608) | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(negUnitSimplification, [status(thm)], [c_62, c_52, c_438])).
% 3.33/1.50  tff(c_324, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_78])).
% 3.33/1.50  tff(c_443, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_440, c_324])).
% 3.33/1.50  tff(c_446, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_38, c_79, c_40, c_319, c_443])).
% 3.33/1.50  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_446])).
% 3.33/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  Inference rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Ref     : 0
% 3.33/1.50  #Sup     : 65
% 3.33/1.50  #Fact    : 0
% 3.33/1.50  #Define  : 0
% 3.33/1.50  #Split   : 2
% 3.33/1.50  #Chain   : 0
% 3.33/1.50  #Close   : 0
% 3.33/1.50  
% 3.33/1.50  Ordering : KBO
% 3.33/1.50  
% 3.33/1.50  Simplification rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Subsume      : 14
% 3.33/1.50  #Demod        : 149
% 3.33/1.50  #Tautology    : 34
% 3.33/1.50  #SimpNegUnit  : 6
% 3.33/1.50  #BackRed      : 0
% 3.33/1.50  
% 3.33/1.50  #Partial instantiations: 0
% 3.33/1.50  #Strategies tried      : 1
% 3.33/1.50  
% 3.33/1.50  Timing (in seconds)
% 3.33/1.50  ----------------------
% 3.33/1.50  Preprocessing        : 0.42
% 3.33/1.50  Parsing              : 0.21
% 3.33/1.50  CNF conversion       : 0.06
% 3.33/1.50  Main loop            : 0.31
% 3.33/1.50  Inferencing          : 0.11
% 3.33/1.50  Reduction            : 0.10
% 3.33/1.50  Demodulation         : 0.07
% 3.33/1.50  BG Simplification    : 0.02
% 3.33/1.50  Subsumption          : 0.06
% 3.33/1.50  Abstraction          : 0.01
% 3.33/1.50  MUC search           : 0.00
% 3.33/1.50  Cooper               : 0.00
% 3.33/1.50  Total                : 0.77
% 3.33/1.50  Index Insertion      : 0.00
% 3.33/1.50  Index Deletion       : 0.00
% 3.33/1.50  Index Matching       : 0.00
% 3.33/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
