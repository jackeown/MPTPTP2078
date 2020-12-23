%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 286 expanded)
%              Number of leaves         :   40 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  347 (2311 expanded)
%              Number of equality atoms :    6 ( 104 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(f_278,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

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

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_168,axiom,(
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

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_36,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_84,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_118,plain,(
    ! [B_545,A_546] :
      ( v2_pre_topc(B_545)
      | ~ m1_pre_topc(B_545,A_546)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_133,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_124])).

tff(c_91,plain,(
    ! [B_539,A_540] :
      ( l1_pre_topc(B_539)
      | ~ m1_pre_topc(B_539,A_540)
      | ~ l1_pre_topc(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_106,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_18,plain,(
    ! [B_18,A_16] :
      ( r2_hidden(B_18,k1_connsp_2(A_16,B_18))
      | ~ m1_subset_1(B_18,u1_struct_0(A_16))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_178,plain,(
    ! [A_563,B_564] :
      ( m1_subset_1(k1_connsp_2(A_563,B_564),k1_zfmisc_1(u1_struct_0(A_563)))
      | ~ m1_subset_1(B_564,u1_struct_0(A_563))
      | ~ l1_pre_topc(A_563)
      | ~ v2_pre_topc(A_563)
      | v2_struct_0(A_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_203,plain,(
    ! [A_567,A_568,B_569] :
      ( ~ v1_xboole_0(u1_struct_0(A_567))
      | ~ r2_hidden(A_568,k1_connsp_2(A_567,B_569))
      | ~ m1_subset_1(B_569,u1_struct_0(A_567))
      | ~ l1_pre_topc(A_567)
      | ~ v2_pre_topc(A_567)
      | v2_struct_0(A_567) ) ),
    inference(resolution,[status(thm)],[c_178,c_10])).

tff(c_218,plain,(
    ! [A_572,B_573] :
      ( ~ v1_xboole_0(u1_struct_0(A_572))
      | ~ m1_subset_1(B_573,u1_struct_0(A_572))
      | ~ l1_pre_topc(A_572)
      | ~ v2_pre_topc(A_572)
      | v2_struct_0(A_572) ) ),
    inference(resolution,[status(thm)],[c_18,c_203])).

tff(c_221,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_218])).

tff(c_227,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_106,c_221])).

tff(c_228,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_227])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_26,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_233,plain,(
    ! [B_574,A_575] :
      ( v3_pre_topc(u1_struct_0(B_574),A_575)
      | ~ v1_tsep_1(B_574,A_575)
      | ~ m1_subset_1(u1_struct_0(B_574),k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ m1_pre_topc(B_574,A_575)
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_237,plain,(
    ! [B_28,A_26] :
      ( v3_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v1_tsep_1(B_28,A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_233])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_83,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_74])).

tff(c_139,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_80])).

tff(c_175,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_82])).

tff(c_252,plain,(
    ! [C_594,D_590,F_595,E_592,B_591,H_589,A_593] :
      ( r1_tmap_1(D_590,A_593,E_592,H_589)
      | ~ r1_tmap_1(C_594,A_593,k3_tmap_1(B_591,A_593,D_590,C_594,E_592),H_589)
      | ~ r1_tarski(F_595,u1_struct_0(C_594))
      | ~ r2_hidden(H_589,F_595)
      | ~ v3_pre_topc(F_595,B_591)
      | ~ m1_subset_1(H_589,u1_struct_0(C_594))
      | ~ m1_subset_1(H_589,u1_struct_0(D_590))
      | ~ m1_subset_1(F_595,k1_zfmisc_1(u1_struct_0(B_591)))
      | ~ m1_pre_topc(C_594,D_590)
      | ~ m1_subset_1(E_592,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_590),u1_struct_0(A_593))))
      | ~ v1_funct_2(E_592,u1_struct_0(D_590),u1_struct_0(A_593))
      | ~ v1_funct_1(E_592)
      | ~ m1_pre_topc(D_590,B_591)
      | v2_struct_0(D_590)
      | ~ m1_pre_topc(C_594,B_591)
      | v2_struct_0(C_594)
      | ~ l1_pre_topc(B_591)
      | ~ v2_pre_topc(B_591)
      | v2_struct_0(B_591)
      | ~ l1_pre_topc(A_593)
      | ~ v2_pre_topc(A_593)
      | v2_struct_0(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_256,plain,(
    ! [F_595] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
      | ~ r1_tarski(F_595,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_595)
      | ~ v3_pre_topc(F_595,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_595,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_175,c_252])).

tff(c_263,plain,(
    ! [F_595] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
      | ~ r1_tarski(F_595,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_595)
      | ~ v3_pre_topc(F_595,'#skF_2')
      | ~ m1_subset_1(F_595,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_50,c_48,c_42,c_40,c_84,c_256])).

tff(c_265,plain,(
    ! [F_596] :
      ( ~ r1_tarski(F_596,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_596)
      | ~ v3_pre_topc(F_596,'#skF_2')
      | ~ m1_subset_1(F_596,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_139,c_263])).

tff(c_273,plain,(
    ! [B_28] :
      ( ~ r1_tarski(u1_struct_0(B_28),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_28))
      | ~ v3_pre_topc(u1_struct_0(B_28),'#skF_2')
      | ~ m1_pre_topc(B_28,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_265])).

tff(c_281,plain,(
    ! [B_597] :
      ( ~ r1_tarski(u1_struct_0(B_597),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_597))
      | ~ v3_pre_topc(u1_struct_0(B_597),'#skF_2')
      | ~ m1_pre_topc(B_597,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_273])).

tff(c_285,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_281])).

tff(c_288,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_285])).

tff(c_289,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_293,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_237,c_289])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_64,c_46,c_293])).

tff(c_298,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_308,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_298])).

tff(c_311,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_308])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_311])).

tff(c_315,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_416,plain,(
    ! [C_630,A_633,E_634,B_632,G_635,D_631] :
      ( r1_tmap_1(D_631,B_632,k3_tmap_1(A_633,B_632,C_630,D_631,E_634),G_635)
      | ~ r1_tmap_1(C_630,B_632,E_634,G_635)
      | ~ m1_pre_topc(D_631,C_630)
      | ~ m1_subset_1(G_635,u1_struct_0(D_631))
      | ~ m1_subset_1(G_635,u1_struct_0(C_630))
      | ~ m1_subset_1(E_634,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_630),u1_struct_0(B_632))))
      | ~ v1_funct_2(E_634,u1_struct_0(C_630),u1_struct_0(B_632))
      | ~ v1_funct_1(E_634)
      | ~ m1_pre_topc(D_631,A_633)
      | v2_struct_0(D_631)
      | ~ m1_pre_topc(C_630,A_633)
      | v2_struct_0(C_630)
      | ~ l1_pre_topc(B_632)
      | ~ v2_pre_topc(B_632)
      | v2_struct_0(B_632)
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_418,plain,(
    ! [D_631,A_633,G_635] :
      ( r1_tmap_1(D_631,'#skF_1',k3_tmap_1(A_633,'#skF_1','#skF_4',D_631,'#skF_5'),G_635)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_635)
      | ~ m1_pre_topc(D_631,'#skF_4')
      | ~ m1_subset_1(G_635,u1_struct_0(D_631))
      | ~ m1_subset_1(G_635,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_631,A_633)
      | v2_struct_0(D_631)
      | ~ m1_pre_topc('#skF_4',A_633)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(resolution,[status(thm)],[c_48,c_416])).

tff(c_421,plain,(
    ! [D_631,A_633,G_635] :
      ( r1_tmap_1(D_631,'#skF_1',k3_tmap_1(A_633,'#skF_1','#skF_4',D_631,'#skF_5'),G_635)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_635)
      | ~ m1_pre_topc(D_631,'#skF_4')
      | ~ m1_subset_1(G_635,u1_struct_0(D_631))
      | ~ m1_subset_1(G_635,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_631,A_633)
      | v2_struct_0(D_631)
      | ~ m1_pre_topc('#skF_4',A_633)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_52,c_50,c_418])).

tff(c_428,plain,(
    ! [D_638,A_639,G_640] :
      ( r1_tmap_1(D_638,'#skF_1',k3_tmap_1(A_639,'#skF_1','#skF_4',D_638,'#skF_5'),G_640)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_640)
      | ~ m1_pre_topc(D_638,'#skF_4')
      | ~ m1_subset_1(G_640,u1_struct_0(D_638))
      | ~ m1_subset_1(G_640,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_638,A_639)
      | v2_struct_0(D_638)
      | ~ m1_pre_topc('#skF_4',A_639)
      | ~ l1_pre_topc(A_639)
      | ~ v2_pre_topc(A_639)
      | v2_struct_0(A_639) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_56,c_421])).

tff(c_314,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_431,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_428,c_314])).

tff(c_434,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_54,c_58,c_40,c_84,c_42,c_315,c_431])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.48  
% 3.47/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.48  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.47/1.48  
% 3.47/1.48  %Foreground sorts:
% 3.47/1.48  
% 3.47/1.48  
% 3.47/1.48  %Background operators:
% 3.47/1.48  
% 3.47/1.48  
% 3.47/1.48  %Foreground operators:
% 3.47/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.48  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.47/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.48  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.47/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.47/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.47/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.48  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.47/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.47/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.47/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.48  
% 3.66/1.50  tff(f_278, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.66/1.50  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.66/1.50  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.66/1.50  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.66/1.50  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.66/1.50  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.66/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.66/1.50  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.66/1.50  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.66/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.66/1.50  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 3.66/1.50  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.66/1.50  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_36, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_84, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 3.66/1.50  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_118, plain, (![B_545, A_546]: (v2_pre_topc(B_545) | ~m1_pre_topc(B_545, A_546) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.66/1.50  tff(c_124, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_118])).
% 3.66/1.50  tff(c_133, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_124])).
% 3.66/1.50  tff(c_91, plain, (![B_539, A_540]: (l1_pre_topc(B_539) | ~m1_pre_topc(B_539, A_540) | ~l1_pre_topc(A_540))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.66/1.50  tff(c_97, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_91])).
% 3.66/1.50  tff(c_106, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97])).
% 3.66/1.50  tff(c_18, plain, (![B_18, A_16]: (r2_hidden(B_18, k1_connsp_2(A_16, B_18)) | ~m1_subset_1(B_18, u1_struct_0(A_16)) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.66/1.50  tff(c_178, plain, (![A_563, B_564]: (m1_subset_1(k1_connsp_2(A_563, B_564), k1_zfmisc_1(u1_struct_0(A_563))) | ~m1_subset_1(B_564, u1_struct_0(A_563)) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563) | v2_struct_0(A_563))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.66/1.50  tff(c_10, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.66/1.50  tff(c_203, plain, (![A_567, A_568, B_569]: (~v1_xboole_0(u1_struct_0(A_567)) | ~r2_hidden(A_568, k1_connsp_2(A_567, B_569)) | ~m1_subset_1(B_569, u1_struct_0(A_567)) | ~l1_pre_topc(A_567) | ~v2_pre_topc(A_567) | v2_struct_0(A_567))), inference(resolution, [status(thm)], [c_178, c_10])).
% 3.66/1.50  tff(c_218, plain, (![A_572, B_573]: (~v1_xboole_0(u1_struct_0(A_572)) | ~m1_subset_1(B_573, u1_struct_0(A_572)) | ~l1_pre_topc(A_572) | ~v2_pre_topc(A_572) | v2_struct_0(A_572))), inference(resolution, [status(thm)], [c_18, c_203])).
% 3.66/1.50  tff(c_221, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_84, c_218])).
% 3.66/1.50  tff(c_227, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_106, c_221])).
% 3.66/1.50  tff(c_228, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_227])).
% 3.66/1.50  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.50  tff(c_46, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_26, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.66/1.50  tff(c_233, plain, (![B_574, A_575]: (v3_pre_topc(u1_struct_0(B_574), A_575) | ~v1_tsep_1(B_574, A_575) | ~m1_subset_1(u1_struct_0(B_574), k1_zfmisc_1(u1_struct_0(A_575))) | ~m1_pre_topc(B_574, A_575) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.66/1.50  tff(c_237, plain, (![B_28, A_26]: (v3_pre_topc(u1_struct_0(B_28), A_26) | ~v1_tsep_1(B_28, A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_26, c_233])).
% 3.66/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.66/1.50  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_83, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_74])).
% 3.66/1.50  tff(c_139, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_83])).
% 3.66/1.50  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_80, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_278])).
% 3.66/1.50  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_80])).
% 3.66/1.50  tff(c_175, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_139, c_82])).
% 3.66/1.50  tff(c_252, plain, (![C_594, D_590, F_595, E_592, B_591, H_589, A_593]: (r1_tmap_1(D_590, A_593, E_592, H_589) | ~r1_tmap_1(C_594, A_593, k3_tmap_1(B_591, A_593, D_590, C_594, E_592), H_589) | ~r1_tarski(F_595, u1_struct_0(C_594)) | ~r2_hidden(H_589, F_595) | ~v3_pre_topc(F_595, B_591) | ~m1_subset_1(H_589, u1_struct_0(C_594)) | ~m1_subset_1(H_589, u1_struct_0(D_590)) | ~m1_subset_1(F_595, k1_zfmisc_1(u1_struct_0(B_591))) | ~m1_pre_topc(C_594, D_590) | ~m1_subset_1(E_592, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_590), u1_struct_0(A_593)))) | ~v1_funct_2(E_592, u1_struct_0(D_590), u1_struct_0(A_593)) | ~v1_funct_1(E_592) | ~m1_pre_topc(D_590, B_591) | v2_struct_0(D_590) | ~m1_pre_topc(C_594, B_591) | v2_struct_0(C_594) | ~l1_pre_topc(B_591) | ~v2_pre_topc(B_591) | v2_struct_0(B_591) | ~l1_pre_topc(A_593) | ~v2_pre_topc(A_593) | v2_struct_0(A_593))), inference(cnfTransformation, [status(thm)], [f_225])).
% 3.66/1.50  tff(c_256, plain, (![F_595]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~r1_tarski(F_595, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_595) | ~v3_pre_topc(F_595, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_595, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_175, c_252])).
% 3.66/1.50  tff(c_263, plain, (![F_595]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~r1_tarski(F_595, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_595) | ~v3_pre_topc(F_595, '#skF_2') | ~m1_subset_1(F_595, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_50, c_48, c_42, c_40, c_84, c_256])).
% 3.66/1.50  tff(c_265, plain, (![F_596]: (~r1_tarski(F_596, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_596) | ~v3_pre_topc(F_596, '#skF_2') | ~m1_subset_1(F_596, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_139, c_263])).
% 3.66/1.50  tff(c_273, plain, (![B_28]: (~r1_tarski(u1_struct_0(B_28), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_28)) | ~v3_pre_topc(u1_struct_0(B_28), '#skF_2') | ~m1_pre_topc(B_28, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_265])).
% 3.66/1.50  tff(c_281, plain, (![B_597]: (~r1_tarski(u1_struct_0(B_597), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_597)) | ~v3_pre_topc(u1_struct_0(B_597), '#skF_2') | ~m1_pre_topc(B_597, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_273])).
% 3.66/1.50  tff(c_285, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_281])).
% 3.66/1.50  tff(c_288, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_285])).
% 3.66/1.50  tff(c_289, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_288])).
% 3.66/1.50  tff(c_293, plain, (~v1_tsep_1('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_237, c_289])).
% 3.66/1.50  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_64, c_46, c_293])).
% 3.66/1.50  tff(c_298, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_288])).
% 3.66/1.50  tff(c_308, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_298])).
% 3.66/1.50  tff(c_311, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_308])).
% 3.66/1.50  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_311])).
% 3.66/1.50  tff(c_315, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 3.66/1.50  tff(c_416, plain, (![C_630, A_633, E_634, B_632, G_635, D_631]: (r1_tmap_1(D_631, B_632, k3_tmap_1(A_633, B_632, C_630, D_631, E_634), G_635) | ~r1_tmap_1(C_630, B_632, E_634, G_635) | ~m1_pre_topc(D_631, C_630) | ~m1_subset_1(G_635, u1_struct_0(D_631)) | ~m1_subset_1(G_635, u1_struct_0(C_630)) | ~m1_subset_1(E_634, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_630), u1_struct_0(B_632)))) | ~v1_funct_2(E_634, u1_struct_0(C_630), u1_struct_0(B_632)) | ~v1_funct_1(E_634) | ~m1_pre_topc(D_631, A_633) | v2_struct_0(D_631) | ~m1_pre_topc(C_630, A_633) | v2_struct_0(C_630) | ~l1_pre_topc(B_632) | ~v2_pre_topc(B_632) | v2_struct_0(B_632) | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.66/1.50  tff(c_418, plain, (![D_631, A_633, G_635]: (r1_tmap_1(D_631, '#skF_1', k3_tmap_1(A_633, '#skF_1', '#skF_4', D_631, '#skF_5'), G_635) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_635) | ~m1_pre_topc(D_631, '#skF_4') | ~m1_subset_1(G_635, u1_struct_0(D_631)) | ~m1_subset_1(G_635, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_631, A_633) | v2_struct_0(D_631) | ~m1_pre_topc('#skF_4', A_633) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(resolution, [status(thm)], [c_48, c_416])).
% 3.66/1.50  tff(c_421, plain, (![D_631, A_633, G_635]: (r1_tmap_1(D_631, '#skF_1', k3_tmap_1(A_633, '#skF_1', '#skF_4', D_631, '#skF_5'), G_635) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_635) | ~m1_pre_topc(D_631, '#skF_4') | ~m1_subset_1(G_635, u1_struct_0(D_631)) | ~m1_subset_1(G_635, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_631, A_633) | v2_struct_0(D_631) | ~m1_pre_topc('#skF_4', A_633) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_52, c_50, c_418])).
% 3.66/1.50  tff(c_428, plain, (![D_638, A_639, G_640]: (r1_tmap_1(D_638, '#skF_1', k3_tmap_1(A_639, '#skF_1', '#skF_4', D_638, '#skF_5'), G_640) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_640) | ~m1_pre_topc(D_638, '#skF_4') | ~m1_subset_1(G_640, u1_struct_0(D_638)) | ~m1_subset_1(G_640, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_638, A_639) | v2_struct_0(D_638) | ~m1_pre_topc('#skF_4', A_639) | ~l1_pre_topc(A_639) | ~v2_pre_topc(A_639) | v2_struct_0(A_639))), inference(negUnitSimplification, [status(thm)], [c_72, c_56, c_421])).
% 3.66/1.50  tff(c_314, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 3.66/1.50  tff(c_431, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_428, c_314])).
% 3.66/1.50  tff(c_434, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_54, c_58, c_40, c_84, c_42, c_315, c_431])).
% 3.66/1.50  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_434])).
% 3.66/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.50  
% 3.66/1.50  Inference rules
% 3.66/1.50  ----------------------
% 3.66/1.50  #Ref     : 0
% 3.66/1.50  #Sup     : 60
% 3.66/1.50  #Fact    : 0
% 3.66/1.50  #Define  : 0
% 3.66/1.50  #Split   : 4
% 3.66/1.50  #Chain   : 0
% 3.66/1.50  #Close   : 0
% 3.66/1.50  
% 3.66/1.50  Ordering : KBO
% 3.66/1.50  
% 3.66/1.50  Simplification rules
% 3.66/1.50  ----------------------
% 3.66/1.50  #Subsume      : 11
% 3.66/1.50  #Demod        : 110
% 3.66/1.50  #Tautology    : 25
% 3.66/1.50  #SimpNegUnit  : 13
% 3.66/1.50  #BackRed      : 0
% 3.66/1.50  
% 3.66/1.50  #Partial instantiations: 0
% 3.66/1.50  #Strategies tried      : 1
% 3.66/1.50  
% 3.66/1.50  Timing (in seconds)
% 3.66/1.50  ----------------------
% 3.66/1.51  Preprocessing        : 0.43
% 3.66/1.51  Parsing              : 0.22
% 3.66/1.51  CNF conversion       : 0.07
% 3.66/1.51  Main loop            : 0.29
% 3.66/1.51  Inferencing          : 0.10
% 3.66/1.51  Reduction            : 0.09
% 3.66/1.51  Demodulation         : 0.07
% 3.66/1.51  BG Simplification    : 0.02
% 3.66/1.51  Subsumption          : 0.06
% 3.66/1.51  Abstraction          : 0.01
% 3.66/1.51  MUC search           : 0.00
% 3.66/1.51  Cooper               : 0.00
% 3.66/1.51  Total                : 0.76
% 3.66/1.51  Index Insertion      : 0.00
% 3.66/1.51  Index Deletion       : 0.00
% 3.66/1.51  Index Matching       : 0.00
% 3.66/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
