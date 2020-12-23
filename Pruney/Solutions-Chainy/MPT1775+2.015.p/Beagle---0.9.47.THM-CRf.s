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
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 646 expanded)
%              Number of leaves         :   42 ( 266 expanded)
%              Depth                    :   24
%              Number of atoms          :  409 (5112 expanded)
%              Number of equality atoms :    5 ( 214 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_276,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_103,axiom,(
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

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_56,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_40,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_91,plain,(
    ! [B_556,A_557] :
      ( l1_pre_topc(B_556)
      | ~ m1_pre_topc(B_556,A_557)
      | ~ l1_pre_topc(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_103,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_106,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_112,plain,(
    ! [B_561,A_562] :
      ( v2_pre_topc(B_561)
      | ~ m1_pre_topc(B_561,A_562)
      | ~ l1_pre_topc(A_562)
      | ~ v2_pre_topc(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_112])).

tff(c_127,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_118])).

tff(c_48,plain,(
    v1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_30,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_292,plain,(
    ! [B_583,A_584] :
      ( v3_pre_topc(u1_struct_0(B_583),A_584)
      | ~ v1_tsep_1(B_583,A_584)
      | ~ m1_subset_1(u1_struct_0(B_583),k1_zfmisc_1(u1_struct_0(A_584)))
      | ~ m1_pre_topc(B_583,A_584)
      | ~ l1_pre_topc(A_584)
      | ~ v2_pre_topc(A_584) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_296,plain,(
    ! [B_45,A_43] :
      ( v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v1_tsep_1(B_45,A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_292])).

tff(c_304,plain,(
    ! [A_591,B_592,C_593] :
      ( r1_tarski('#skF_1'(A_591,B_592,C_593),B_592)
      | ~ r2_hidden(C_593,B_592)
      | ~ m1_subset_1(C_593,u1_struct_0(A_591))
      | ~ v3_pre_topc(B_592,A_591)
      | ~ m1_subset_1(B_592,k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591)
      | v2_struct_0(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_307,plain,(
    ! [A_43,B_45,C_593] :
      ( r1_tarski('#skF_1'(A_43,u1_struct_0(B_45),C_593),u1_struct_0(B_45))
      | ~ r2_hidden(C_593,u1_struct_0(B_45))
      | ~ m1_subset_1(C_593,u1_struct_0(A_43))
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_304])).

tff(c_22,plain,(
    ! [A_11,B_25,C_32] :
      ( m1_subset_1('#skF_1'(A_11,B_25,C_32),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0(A_11))
      | ~ v3_pre_topc(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_133,plain,(
    ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_52,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_173,plain,(
    r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_83])).

tff(c_343,plain,(
    ! [F_625,E_626,D_627,C_628,A_631,B_629,H_630] :
      ( r1_tmap_1(D_627,B_629,E_626,H_630)
      | ~ r1_tmap_1(C_628,B_629,k3_tmap_1(A_631,B_629,D_627,C_628,E_626),H_630)
      | ~ m1_connsp_2(F_625,D_627,H_630)
      | ~ r1_tarski(F_625,u1_struct_0(C_628))
      | ~ m1_subset_1(H_630,u1_struct_0(C_628))
      | ~ m1_subset_1(H_630,u1_struct_0(D_627))
      | ~ m1_subset_1(F_625,k1_zfmisc_1(u1_struct_0(D_627)))
      | ~ m1_pre_topc(C_628,D_627)
      | ~ m1_subset_1(E_626,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_627),u1_struct_0(B_629))))
      | ~ v1_funct_2(E_626,u1_struct_0(D_627),u1_struct_0(B_629))
      | ~ v1_funct_1(E_626)
      | ~ m1_pre_topc(D_627,A_631)
      | v2_struct_0(D_627)
      | ~ m1_pre_topc(C_628,A_631)
      | v2_struct_0(C_628)
      | ~ l1_pre_topc(B_629)
      | ~ v2_pre_topc(B_629)
      | v2_struct_0(B_629)
      | ~ l1_pre_topc(A_631)
      | ~ v2_pre_topc(A_631)
      | v2_struct_0(A_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_347,plain,(
    ! [F_625] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ m1_connsp_2(F_625,'#skF_6','#skF_8')
      | ~ r1_tarski(F_625,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_625,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_6','#skF_3')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_173,c_343])).

tff(c_354,plain,(
    ! [F_625] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ m1_connsp_2(F_625,'#skF_6','#skF_8')
      | ~ r1_tarski(F_625,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_625,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_46,c_44,c_85,c_347])).

tff(c_356,plain,(
    ! [F_632] :
      ( ~ m1_connsp_2(F_632,'#skF_6','#skF_8')
      | ~ r1_tarski(F_632,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_632,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_133,c_354])).

tff(c_360,plain,(
    ! [B_25,C_32] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_25,C_32),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_25,C_32),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_25,'#skF_6')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_356])).

tff(c_367,plain,(
    ! [B_25,C_32] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_25,C_32),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_25,C_32),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_25,'#skF_6')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_106,c_360])).

tff(c_373,plain,(
    ! [B_634,C_635] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_634,C_635),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_634,C_635),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_635,B_634)
      | ~ m1_subset_1(C_635,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_634,'#skF_6')
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_367])).

tff(c_377,plain,(
    ! [C_593] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_593),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_307,c_373])).

tff(c_380,plain,(
    ! [C_593] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_593),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_46,c_127,c_377])).

tff(c_381,plain,(
    ! [C_593] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_593),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_380])).

tff(c_382,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_385,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_296,c_382])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_46,c_127,c_48,c_385])).

tff(c_391,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_308,plain,(
    ! [A_594,B_595,C_596] :
      ( m1_connsp_2('#skF_1'(A_594,B_595,C_596),A_594,C_596)
      | ~ r2_hidden(C_596,B_595)
      | ~ m1_subset_1(C_596,u1_struct_0(A_594))
      | ~ v3_pre_topc(B_595,A_594)
      | ~ m1_subset_1(B_595,k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_311,plain,(
    ! [A_43,B_45,C_596] :
      ( m1_connsp_2('#skF_1'(A_43,u1_struct_0(B_45),C_596),A_43,C_596)
      | ~ r2_hidden(C_596,u1_struct_0(B_45))
      | ~ m1_subset_1(C_596,u1_struct_0(A_43))
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_30,c_308])).

tff(c_390,plain,(
    ! [C_593] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_593),'#skF_6','#skF_8')
      | ~ r2_hidden(C_593,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_593,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_399,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_402,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_399])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_46,c_402])).

tff(c_432,plain,(
    ! [C_640] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_640),'#skF_6','#skF_8')
      | ~ r2_hidden(C_640,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_436,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_311,c_432])).

tff(c_439,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_46,c_127,c_391,c_44,c_436])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_439])).

tff(c_443,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2,c_440])).

tff(c_446,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_443])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_449,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_452,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_449])).

tff(c_460,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_452])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_460])).

tff(c_466,plain,(
    r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_669,plain,(
    ! [G_700,E_702,C_699,A_697,B_698,D_701] :
      ( r1_tmap_1(D_701,B_698,k3_tmap_1(A_697,B_698,C_699,D_701,E_702),G_700)
      | ~ r1_tmap_1(C_699,B_698,E_702,G_700)
      | ~ m1_pre_topc(D_701,C_699)
      | ~ m1_subset_1(G_700,u1_struct_0(D_701))
      | ~ m1_subset_1(G_700,u1_struct_0(C_699))
      | ~ m1_subset_1(E_702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_699),u1_struct_0(B_698))))
      | ~ v1_funct_2(E_702,u1_struct_0(C_699),u1_struct_0(B_698))
      | ~ v1_funct_1(E_702)
      | ~ m1_pre_topc(D_701,A_697)
      | v2_struct_0(D_701)
      | ~ m1_pre_topc(C_699,A_697)
      | v2_struct_0(C_699)
      | ~ l1_pre_topc(B_698)
      | ~ v2_pre_topc(B_698)
      | v2_struct_0(B_698)
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_671,plain,(
    ! [D_701,A_697,G_700] :
      ( r1_tmap_1(D_701,'#skF_4',k3_tmap_1(A_697,'#skF_4','#skF_6',D_701,'#skF_7'),G_700)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_700)
      | ~ m1_pre_topc(D_701,'#skF_6')
      | ~ m1_subset_1(G_700,u1_struct_0(D_701))
      | ~ m1_subset_1(G_700,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_701,A_697)
      | v2_struct_0(D_701)
      | ~ m1_pre_topc('#skF_6',A_697)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_50,c_669])).

tff(c_674,plain,(
    ! [D_701,A_697,G_700] :
      ( r1_tmap_1(D_701,'#skF_4',k3_tmap_1(A_697,'#skF_4','#skF_6',D_701,'#skF_7'),G_700)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_700)
      | ~ m1_pre_topc(D_701,'#skF_6')
      | ~ m1_subset_1(G_700,u1_struct_0(D_701))
      | ~ m1_subset_1(G_700,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_701,A_697)
      | v2_struct_0(D_701)
      | ~ m1_pre_topc('#skF_6',A_697)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_671])).

tff(c_676,plain,(
    ! [D_703,A_704,G_705] :
      ( r1_tmap_1(D_703,'#skF_4',k3_tmap_1(A_704,'#skF_4','#skF_6',D_703,'#skF_7'),G_705)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_705)
      | ~ m1_pre_topc(D_703,'#skF_6')
      | ~ m1_subset_1(G_705,u1_struct_0(D_703))
      | ~ m1_subset_1(G_705,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_703,A_704)
      | v2_struct_0(D_703)
      | ~ m1_pre_topc('#skF_6',A_704)
      | ~ l1_pre_topc(A_704)
      | ~ v2_pre_topc(A_704)
      | v2_struct_0(A_704) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_674])).

tff(c_465,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_679,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_676,c_465])).

tff(c_682,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_44,c_85,c_46,c_466,c_679])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.58  
% 3.88/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.59  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 3.88/1.59  
% 3.88/1.59  %Foreground sorts:
% 3.88/1.59  
% 3.88/1.59  
% 3.88/1.59  %Background operators:
% 3.88/1.59  
% 3.88/1.59  
% 3.88/1.59  %Foreground operators:
% 3.88/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.88/1.59  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.88/1.59  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.88/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.88/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.88/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.88/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.88/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.88/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.88/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.88/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.59  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.88/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.88/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.88/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.88/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.88/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.59  
% 4.00/1.61  tff(f_276, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.00/1.61  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.00/1.61  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.00/1.61  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.00/1.61  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.00/1.61  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.00/1.61  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.00/1.61  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 4.00/1.61  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.00/1.61  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.00/1.61  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.00/1.61  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_56, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_40, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_42, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 4.00/1.61  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_91, plain, (![B_556, A_557]: (l1_pre_topc(B_556) | ~m1_pre_topc(B_556, A_557) | ~l1_pre_topc(A_557))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.00/1.61  tff(c_94, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_91])).
% 4.00/1.61  tff(c_103, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 4.00/1.61  tff(c_6, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.00/1.61  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.61  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_97, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_91])).
% 4.00/1.61  tff(c_106, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 4.00/1.61  tff(c_112, plain, (![B_561, A_562]: (v2_pre_topc(B_561) | ~m1_pre_topc(B_561, A_562) | ~l1_pre_topc(A_562) | ~v2_pre_topc(A_562))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.00/1.61  tff(c_118, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_112])).
% 4.00/1.61  tff(c_127, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_118])).
% 4.00/1.61  tff(c_48, plain, (v1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_30, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.00/1.61  tff(c_292, plain, (![B_583, A_584]: (v3_pre_topc(u1_struct_0(B_583), A_584) | ~v1_tsep_1(B_583, A_584) | ~m1_subset_1(u1_struct_0(B_583), k1_zfmisc_1(u1_struct_0(A_584))) | ~m1_pre_topc(B_583, A_584) | ~l1_pre_topc(A_584) | ~v2_pre_topc(A_584))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.00/1.61  tff(c_296, plain, (![B_45, A_43]: (v3_pre_topc(u1_struct_0(B_45), A_43) | ~v1_tsep_1(B_45, A_43) | ~v2_pre_topc(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_30, c_292])).
% 4.00/1.61  tff(c_304, plain, (![A_591, B_592, C_593]: (r1_tarski('#skF_1'(A_591, B_592, C_593), B_592) | ~r2_hidden(C_593, B_592) | ~m1_subset_1(C_593, u1_struct_0(A_591)) | ~v3_pre_topc(B_592, A_591) | ~m1_subset_1(B_592, k1_zfmisc_1(u1_struct_0(A_591))) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591) | v2_struct_0(A_591))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.00/1.61  tff(c_307, plain, (![A_43, B_45, C_593]: (r1_tarski('#skF_1'(A_43, u1_struct_0(B_45), C_593), u1_struct_0(B_45)) | ~r2_hidden(C_593, u1_struct_0(B_45)) | ~m1_subset_1(C_593, u1_struct_0(A_43)) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_30, c_304])).
% 4.00/1.61  tff(c_22, plain, (![A_11, B_25, C_32]: (m1_subset_1('#skF_1'(A_11, B_25, C_32), k1_zfmisc_1(u1_struct_0(A_11))) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0(A_11)) | ~v3_pre_topc(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.00/1.61  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_84, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 4.00/1.61  tff(c_133, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_84])).
% 4.00/1.61  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_52, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_82, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_276])).
% 4.00/1.61  tff(c_83, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 4.00/1.61  tff(c_173, plain, (r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_133, c_83])).
% 4.00/1.61  tff(c_343, plain, (![F_625, E_626, D_627, C_628, A_631, B_629, H_630]: (r1_tmap_1(D_627, B_629, E_626, H_630) | ~r1_tmap_1(C_628, B_629, k3_tmap_1(A_631, B_629, D_627, C_628, E_626), H_630) | ~m1_connsp_2(F_625, D_627, H_630) | ~r1_tarski(F_625, u1_struct_0(C_628)) | ~m1_subset_1(H_630, u1_struct_0(C_628)) | ~m1_subset_1(H_630, u1_struct_0(D_627)) | ~m1_subset_1(F_625, k1_zfmisc_1(u1_struct_0(D_627))) | ~m1_pre_topc(C_628, D_627) | ~m1_subset_1(E_626, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_627), u1_struct_0(B_629)))) | ~v1_funct_2(E_626, u1_struct_0(D_627), u1_struct_0(B_629)) | ~v1_funct_1(E_626) | ~m1_pre_topc(D_627, A_631) | v2_struct_0(D_627) | ~m1_pre_topc(C_628, A_631) | v2_struct_0(C_628) | ~l1_pre_topc(B_629) | ~v2_pre_topc(B_629) | v2_struct_0(B_629) | ~l1_pre_topc(A_631) | ~v2_pre_topc(A_631) | v2_struct_0(A_631))), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.61  tff(c_347, plain, (![F_625]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_connsp_2(F_625, '#skF_6', '#skF_8') | ~r1_tarski(F_625, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(F_625, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_173, c_343])).
% 4.00/1.61  tff(c_354, plain, (![F_625]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_connsp_2(F_625, '#skF_6', '#skF_8') | ~r1_tarski(F_625, u1_struct_0('#skF_5')) | ~m1_subset_1(F_625, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_46, c_44, c_85, c_347])).
% 4.00/1.61  tff(c_356, plain, (![F_632]: (~m1_connsp_2(F_632, '#skF_6', '#skF_8') | ~r1_tarski(F_632, u1_struct_0('#skF_5')) | ~m1_subset_1(F_632, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_133, c_354])).
% 4.00/1.61  tff(c_360, plain, (![B_25, C_32]: (~m1_connsp_2('#skF_1'('#skF_6', B_25, C_32), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_25, C_32), u1_struct_0('#skF_5')) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_25, '#skF_6') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_356])).
% 4.00/1.61  tff(c_367, plain, (![B_25, C_32]: (~m1_connsp_2('#skF_1'('#skF_6', B_25, C_32), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_25, C_32), u1_struct_0('#skF_5')) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_25, '#skF_6') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_106, c_360])).
% 4.00/1.61  tff(c_373, plain, (![B_634, C_635]: (~m1_connsp_2('#skF_1'('#skF_6', B_634, C_635), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_634, C_635), u1_struct_0('#skF_5')) | ~r2_hidden(C_635, B_634) | ~m1_subset_1(C_635, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_634, '#skF_6') | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_367])).
% 4.00/1.61  tff(c_377, plain, (![C_593]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_593), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_593, u1_struct_0('#skF_5')) | ~m1_subset_1(C_593, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_307, c_373])).
% 4.00/1.61  tff(c_380, plain, (![C_593]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_593), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_593, u1_struct_0('#skF_5')) | ~m1_subset_1(C_593, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_46, c_127, c_377])).
% 4.00/1.61  tff(c_381, plain, (![C_593]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_593), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_593, u1_struct_0('#skF_5')) | ~m1_subset_1(C_593, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_380])).
% 4.00/1.61  tff(c_382, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_381])).
% 4.00/1.61  tff(c_385, plain, (~v1_tsep_1('#skF_5', '#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_296, c_382])).
% 4.00/1.61  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_46, c_127, c_48, c_385])).
% 4.00/1.61  tff(c_391, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_381])).
% 4.00/1.61  tff(c_308, plain, (![A_594, B_595, C_596]: (m1_connsp_2('#skF_1'(A_594, B_595, C_596), A_594, C_596) | ~r2_hidden(C_596, B_595) | ~m1_subset_1(C_596, u1_struct_0(A_594)) | ~v3_pre_topc(B_595, A_594) | ~m1_subset_1(B_595, k1_zfmisc_1(u1_struct_0(A_594))) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.00/1.61  tff(c_311, plain, (![A_43, B_45, C_596]: (m1_connsp_2('#skF_1'(A_43, u1_struct_0(B_45), C_596), A_43, C_596) | ~r2_hidden(C_596, u1_struct_0(B_45)) | ~m1_subset_1(C_596, u1_struct_0(A_43)) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_30, c_308])).
% 4.00/1.61  tff(c_390, plain, (![C_593]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_593), '#skF_6', '#skF_8') | ~r2_hidden(C_593, u1_struct_0('#skF_5')) | ~m1_subset_1(C_593, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_381])).
% 4.00/1.61  tff(c_399, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_390])).
% 4.00/1.61  tff(c_402, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_30, c_399])).
% 4.00/1.61  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_46, c_402])).
% 4.00/1.61  tff(c_432, plain, (![C_640]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_640), '#skF_6', '#skF_8') | ~r2_hidden(C_640, u1_struct_0('#skF_5')) | ~m1_subset_1(C_640, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_390])).
% 4.00/1.61  tff(c_436, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_311, c_432])).
% 4.00/1.61  tff(c_439, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_46, c_127, c_391, c_44, c_436])).
% 4.00/1.61  tff(c_440, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_439])).
% 4.00/1.61  tff(c_443, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2, c_440])).
% 4.00/1.61  tff(c_446, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_443])).
% 4.00/1.61  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.00/1.61  tff(c_449, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_446, c_10])).
% 4.00/1.61  tff(c_452, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_449])).
% 4.00/1.61  tff(c_460, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6, c_452])).
% 4.00/1.61  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_460])).
% 4.00/1.61  tff(c_466, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.00/1.61  tff(c_669, plain, (![G_700, E_702, C_699, A_697, B_698, D_701]: (r1_tmap_1(D_701, B_698, k3_tmap_1(A_697, B_698, C_699, D_701, E_702), G_700) | ~r1_tmap_1(C_699, B_698, E_702, G_700) | ~m1_pre_topc(D_701, C_699) | ~m1_subset_1(G_700, u1_struct_0(D_701)) | ~m1_subset_1(G_700, u1_struct_0(C_699)) | ~m1_subset_1(E_702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_699), u1_struct_0(B_698)))) | ~v1_funct_2(E_702, u1_struct_0(C_699), u1_struct_0(B_698)) | ~v1_funct_1(E_702) | ~m1_pre_topc(D_701, A_697) | v2_struct_0(D_701) | ~m1_pre_topc(C_699, A_697) | v2_struct_0(C_699) | ~l1_pre_topc(B_698) | ~v2_pre_topc(B_698) | v2_struct_0(B_698) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.00/1.61  tff(c_671, plain, (![D_701, A_697, G_700]: (r1_tmap_1(D_701, '#skF_4', k3_tmap_1(A_697, '#skF_4', '#skF_6', D_701, '#skF_7'), G_700) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_700) | ~m1_pre_topc(D_701, '#skF_6') | ~m1_subset_1(G_700, u1_struct_0(D_701)) | ~m1_subset_1(G_700, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_701, A_697) | v2_struct_0(D_701) | ~m1_pre_topc('#skF_6', A_697) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(resolution, [status(thm)], [c_50, c_669])).
% 4.00/1.61  tff(c_674, plain, (![D_701, A_697, G_700]: (r1_tmap_1(D_701, '#skF_4', k3_tmap_1(A_697, '#skF_4', '#skF_6', D_701, '#skF_7'), G_700) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_700) | ~m1_pre_topc(D_701, '#skF_6') | ~m1_subset_1(G_700, u1_struct_0(D_701)) | ~m1_subset_1(G_700, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_701, A_697) | v2_struct_0(D_701) | ~m1_pre_topc('#skF_6', A_697) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_671])).
% 4.00/1.61  tff(c_676, plain, (![D_703, A_704, G_705]: (r1_tmap_1(D_703, '#skF_4', k3_tmap_1(A_704, '#skF_4', '#skF_6', D_703, '#skF_7'), G_705) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_705) | ~m1_pre_topc(D_703, '#skF_6') | ~m1_subset_1(G_705, u1_struct_0(D_703)) | ~m1_subset_1(G_705, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_703, A_704) | v2_struct_0(D_703) | ~m1_pre_topc('#skF_6', A_704) | ~l1_pre_topc(A_704) | ~v2_pre_topc(A_704) | v2_struct_0(A_704))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_674])).
% 4.00/1.61  tff(c_465, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 4.00/1.61  tff(c_679, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_676, c_465])).
% 4.00/1.61  tff(c_682, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_44, c_85, c_46, c_466, c_679])).
% 4.00/1.61  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_682])).
% 4.00/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.61  
% 4.00/1.61  Inference rules
% 4.00/1.61  ----------------------
% 4.00/1.61  #Ref     : 0
% 4.00/1.61  #Sup     : 110
% 4.00/1.61  #Fact    : 0
% 4.00/1.61  #Define  : 0
% 4.00/1.61  #Split   : 6
% 4.00/1.61  #Chain   : 0
% 4.00/1.61  #Close   : 0
% 4.00/1.61  
% 4.00/1.61  Ordering : KBO
% 4.00/1.61  
% 4.00/1.61  Simplification rules
% 4.00/1.61  ----------------------
% 4.00/1.61  #Subsume      : 21
% 4.00/1.61  #Demod        : 216
% 4.00/1.61  #Tautology    : 44
% 4.00/1.61  #SimpNegUnit  : 14
% 4.00/1.61  #BackRed      : 0
% 4.00/1.61  
% 4.00/1.61  #Partial instantiations: 0
% 4.00/1.61  #Strategies tried      : 1
% 4.00/1.61  
% 4.00/1.61  Timing (in seconds)
% 4.00/1.61  ----------------------
% 4.00/1.62  Preprocessing        : 0.44
% 4.00/1.62  Parsing              : 0.22
% 4.00/1.62  CNF conversion       : 0.07
% 4.00/1.62  Main loop            : 0.38
% 4.00/1.62  Inferencing          : 0.14
% 4.00/1.62  Reduction            : 0.12
% 4.00/1.62  Demodulation         : 0.09
% 4.00/1.62  BG Simplification    : 0.03
% 4.00/1.62  Subsumption          : 0.07
% 4.00/1.62  Abstraction          : 0.02
% 4.00/1.62  MUC search           : 0.00
% 4.00/1.62  Cooper               : 0.00
% 4.00/1.62  Total                : 0.87
% 4.00/1.62  Index Insertion      : 0.00
% 4.00/1.62  Index Deletion       : 0.00
% 4.00/1.62  Index Matching       : 0.00
% 4.00/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
