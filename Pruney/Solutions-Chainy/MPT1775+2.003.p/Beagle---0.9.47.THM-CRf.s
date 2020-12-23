%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 312 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  353 (2370 expanded)
%              Number of equality atoms :    6 ( 109 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_56,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_36,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_115,plain,(
    ! [B_545,A_546] :
      ( v2_pre_topc(B_545)
      | ~ m1_pre_topc(B_545,A_546)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_115])).

tff(c_130,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_121])).

tff(c_88,plain,(
    ! [B_539,A_540] :
      ( l1_pre_topc(B_539)
      | ~ m1_pre_topc(B_539,A_540)
      | ~ l1_pre_topc(A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_103,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_94])).

tff(c_18,plain,(
    ! [B_18,A_16] :
      ( r2_hidden(B_18,k1_connsp_2(A_16,B_18))
      | ~ m1_subset_1(B_18,u1_struct_0(A_16))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_188,plain,(
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

tff(c_250,plain,(
    ! [A_573,A_574,B_575] :
      ( ~ v1_xboole_0(u1_struct_0(A_573))
      | ~ r2_hidden(A_574,k1_connsp_2(A_573,B_575))
      | ~ m1_subset_1(B_575,u1_struct_0(A_573))
      | ~ l1_pre_topc(A_573)
      | ~ v2_pre_topc(A_573)
      | v2_struct_0(A_573) ) ),
    inference(resolution,[status(thm)],[c_188,c_10])).

tff(c_260,plain,(
    ! [A_576,B_577] :
      ( ~ v1_xboole_0(u1_struct_0(A_576))
      | ~ m1_subset_1(B_577,u1_struct_0(A_576))
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | v2_struct_0(A_576) ) ),
    inference(resolution,[status(thm)],[c_18,c_250])).

tff(c_263,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_260])).

tff(c_269,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_103,c_263])).

tff(c_270,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_88])).

tff(c_100,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_91])).

tff(c_118,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_127,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_118])).

tff(c_44,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_26,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_275,plain,(
    ! [B_578,A_579] :
      ( v3_pre_topc(u1_struct_0(B_578),A_579)
      | ~ v1_tsep_1(B_578,A_579)
      | ~ m1_subset_1(u1_struct_0(B_578),k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ m1_pre_topc(B_578,A_579)
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_279,plain,(
    ! [B_28,A_26] :
      ( v3_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v1_tsep_1(B_28,A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_275])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_136,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_48,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_79,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_78])).

tff(c_185,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_79])).

tff(c_292,plain,(
    ! [E_591,D_589,H_588,A_592,F_594,B_590,C_593] :
      ( r1_tmap_1(D_589,B_590,E_591,H_588)
      | ~ r1_tmap_1(C_593,B_590,k3_tmap_1(A_592,B_590,D_589,C_593,E_591),H_588)
      | ~ r1_tarski(F_594,u1_struct_0(C_593))
      | ~ r2_hidden(H_588,F_594)
      | ~ v3_pre_topc(F_594,D_589)
      | ~ m1_subset_1(H_588,u1_struct_0(C_593))
      | ~ m1_subset_1(H_588,u1_struct_0(D_589))
      | ~ m1_subset_1(F_594,k1_zfmisc_1(u1_struct_0(D_589)))
      | ~ m1_pre_topc(C_593,D_589)
      | ~ m1_subset_1(E_591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_589),u1_struct_0(B_590))))
      | ~ v1_funct_2(E_591,u1_struct_0(D_589),u1_struct_0(B_590))
      | ~ v1_funct_1(E_591)
      | ~ m1_pre_topc(D_589,A_592)
      | v2_struct_0(D_589)
      | ~ m1_pre_topc(C_593,A_592)
      | v2_struct_0(C_593)
      | ~ l1_pre_topc(B_590)
      | ~ v2_pre_topc(B_590)
      | v2_struct_0(B_590)
      | ~ l1_pre_topc(A_592)
      | ~ v2_pre_topc(A_592)
      | v2_struct_0(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_294,plain,(
    ! [F_594] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_594,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_594)
      | ~ v3_pre_topc(F_594,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_594,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_185,c_292])).

tff(c_297,plain,(
    ! [F_594] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_594,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_594)
      | ~ v3_pre_topc(F_594,'#skF_4')
      | ~ m1_subset_1(F_594,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_56,c_52,c_50,c_48,c_46,c_42,c_40,c_81,c_294])).

tff(c_299,plain,(
    ! [F_595] :
      ( ~ r1_tarski(F_595,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_595)
      | ~ v3_pre_topc(F_595,'#skF_4')
      | ~ m1_subset_1(F_595,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_58,c_54,c_136,c_297])).

tff(c_307,plain,(
    ! [B_28] :
      ( ~ r1_tarski(u1_struct_0(B_28),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_28))
      | ~ v3_pre_topc(u1_struct_0(B_28),'#skF_4')
      | ~ m1_pre_topc(B_28,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_299])).

tff(c_315,plain,(
    ! [B_596] :
      ( ~ r1_tarski(u1_struct_0(B_596),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_596))
      | ~ v3_pre_topc(u1_struct_0(B_596),'#skF_4')
      | ~ m1_pre_topc(B_596,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_307])).

tff(c_319,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_315])).

tff(c_322,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_319])).

tff(c_323,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_327,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_279,c_323])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_42,c_127,c_44,c_327])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_342,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_345,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_342])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_345])).

tff(c_349,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_499,plain,(
    ! [C_633,D_634,G_638,A_636,E_637,B_635] :
      ( r1_tmap_1(D_634,B_635,k3_tmap_1(A_636,B_635,C_633,D_634,E_637),G_638)
      | ~ r1_tmap_1(C_633,B_635,E_637,G_638)
      | ~ m1_pre_topc(D_634,C_633)
      | ~ m1_subset_1(G_638,u1_struct_0(D_634))
      | ~ m1_subset_1(G_638,u1_struct_0(C_633))
      | ~ m1_subset_1(E_637,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_633),u1_struct_0(B_635))))
      | ~ v1_funct_2(E_637,u1_struct_0(C_633),u1_struct_0(B_635))
      | ~ v1_funct_1(E_637)
      | ~ m1_pre_topc(D_634,A_636)
      | v2_struct_0(D_634)
      | ~ m1_pre_topc(C_633,A_636)
      | v2_struct_0(C_633)
      | ~ l1_pre_topc(B_635)
      | ~ v2_pre_topc(B_635)
      | v2_struct_0(B_635)
      | ~ l1_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_501,plain,(
    ! [D_634,A_636,G_638] :
      ( r1_tmap_1(D_634,'#skF_2',k3_tmap_1(A_636,'#skF_2','#skF_4',D_634,'#skF_5'),G_638)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_638)
      | ~ m1_pre_topc(D_634,'#skF_4')
      | ~ m1_subset_1(G_638,u1_struct_0(D_634))
      | ~ m1_subset_1(G_638,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_634,A_636)
      | v2_struct_0(D_634)
      | ~ m1_pre_topc('#skF_4',A_636)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636) ) ),
    inference(resolution,[status(thm)],[c_46,c_499])).

tff(c_504,plain,(
    ! [D_634,A_636,G_638] :
      ( r1_tmap_1(D_634,'#skF_2',k3_tmap_1(A_636,'#skF_2','#skF_4',D_634,'#skF_5'),G_638)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_638)
      | ~ m1_pre_topc(D_634,'#skF_4')
      | ~ m1_subset_1(G_638,u1_struct_0(D_634))
      | ~ m1_subset_1(G_638,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_634,A_636)
      | v2_struct_0(D_634)
      | ~ m1_pre_topc('#skF_4',A_636)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_48,c_501])).

tff(c_506,plain,(
    ! [D_639,A_640,G_641] :
      ( r1_tmap_1(D_639,'#skF_2',k3_tmap_1(A_640,'#skF_2','#skF_4',D_639,'#skF_5'),G_641)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_641)
      | ~ m1_pre_topc(D_639,'#skF_4')
      | ~ m1_subset_1(G_641,u1_struct_0(D_639))
      | ~ m1_subset_1(G_641,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_639,A_640)
      | v2_struct_0(D_639)
      | ~ m1_pre_topc('#skF_4',A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_54,c_504])).

tff(c_348,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_509,plain,
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
    inference(resolution,[status(thm)],[c_506,c_348])).

tff(c_512,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_52,c_56,c_40,c_81,c_42,c_349,c_509])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_58,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.63  
% 3.42/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.63  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.42/1.63  
% 3.42/1.63  %Foreground sorts:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Background operators:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Foreground operators:
% 3.42/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.63  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.63  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.63  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.42/1.63  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.42/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.42/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.63  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.42/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.42/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.42/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.63  
% 3.77/1.65  tff(f_276, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.77/1.65  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.77/1.65  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.77/1.65  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.77/1.65  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.77/1.65  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.77/1.65  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.77/1.65  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.77/1.65  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.77/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.65  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.77/1.65  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.77/1.65  tff(c_70, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_56, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_36, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_38, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_81, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 3.77/1.65  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_115, plain, (![B_545, A_546]: (v2_pre_topc(B_545) | ~m1_pre_topc(B_545, A_546) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.77/1.65  tff(c_121, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_115])).
% 3.77/1.65  tff(c_130, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_121])).
% 3.77/1.65  tff(c_88, plain, (![B_539, A_540]: (l1_pre_topc(B_539) | ~m1_pre_topc(B_539, A_540) | ~l1_pre_topc(A_540))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.77/1.65  tff(c_94, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_88])).
% 3.77/1.65  tff(c_103, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_94])).
% 3.77/1.65  tff(c_18, plain, (![B_18, A_16]: (r2_hidden(B_18, k1_connsp_2(A_16, B_18)) | ~m1_subset_1(B_18, u1_struct_0(A_16)) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.77/1.65  tff(c_188, plain, (![A_563, B_564]: (m1_subset_1(k1_connsp_2(A_563, B_564), k1_zfmisc_1(u1_struct_0(A_563))) | ~m1_subset_1(B_564, u1_struct_0(A_563)) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563) | v2_struct_0(A_563))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.77/1.65  tff(c_10, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.77/1.65  tff(c_250, plain, (![A_573, A_574, B_575]: (~v1_xboole_0(u1_struct_0(A_573)) | ~r2_hidden(A_574, k1_connsp_2(A_573, B_575)) | ~m1_subset_1(B_575, u1_struct_0(A_573)) | ~l1_pre_topc(A_573) | ~v2_pre_topc(A_573) | v2_struct_0(A_573))), inference(resolution, [status(thm)], [c_188, c_10])).
% 3.77/1.65  tff(c_260, plain, (![A_576, B_577]: (~v1_xboole_0(u1_struct_0(A_576)) | ~m1_subset_1(B_577, u1_struct_0(A_576)) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | v2_struct_0(A_576))), inference(resolution, [status(thm)], [c_18, c_250])).
% 3.77/1.65  tff(c_263, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_81, c_260])).
% 3.77/1.65  tff(c_269, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_103, c_263])).
% 3.77/1.65  tff(c_270, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 3.77/1.65  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.65  tff(c_91, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_88])).
% 3.77/1.65  tff(c_100, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_91])).
% 3.77/1.65  tff(c_118, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_115])).
% 3.77/1.65  tff(c_127, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_118])).
% 3.77/1.65  tff(c_44, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_26, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.65  tff(c_275, plain, (![B_578, A_579]: (v3_pre_topc(u1_struct_0(B_578), A_579) | ~v1_tsep_1(B_578, A_579) | ~m1_subset_1(u1_struct_0(B_578), k1_zfmisc_1(u1_struct_0(A_579))) | ~m1_pre_topc(B_578, A_579) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.77/1.65  tff(c_279, plain, (![B_28, A_26]: (v3_pre_topc(u1_struct_0(B_28), A_26) | ~v1_tsep_1(B_28, A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_26, c_275])).
% 3.77/1.65  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.65  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_72, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_80, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 3.77/1.65  tff(c_136, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_80])).
% 3.77/1.65  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_48, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_78, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.77/1.65  tff(c_79, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_78])).
% 3.77/1.65  tff(c_185, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_136, c_79])).
% 3.77/1.65  tff(c_292, plain, (![E_591, D_589, H_588, A_592, F_594, B_590, C_593]: (r1_tmap_1(D_589, B_590, E_591, H_588) | ~r1_tmap_1(C_593, B_590, k3_tmap_1(A_592, B_590, D_589, C_593, E_591), H_588) | ~r1_tarski(F_594, u1_struct_0(C_593)) | ~r2_hidden(H_588, F_594) | ~v3_pre_topc(F_594, D_589) | ~m1_subset_1(H_588, u1_struct_0(C_593)) | ~m1_subset_1(H_588, u1_struct_0(D_589)) | ~m1_subset_1(F_594, k1_zfmisc_1(u1_struct_0(D_589))) | ~m1_pre_topc(C_593, D_589) | ~m1_subset_1(E_591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_589), u1_struct_0(B_590)))) | ~v1_funct_2(E_591, u1_struct_0(D_589), u1_struct_0(B_590)) | ~v1_funct_1(E_591) | ~m1_pre_topc(D_589, A_592) | v2_struct_0(D_589) | ~m1_pre_topc(C_593, A_592) | v2_struct_0(C_593) | ~l1_pre_topc(B_590) | ~v2_pre_topc(B_590) | v2_struct_0(B_590) | ~l1_pre_topc(A_592) | ~v2_pre_topc(A_592) | v2_struct_0(A_592))), inference(cnfTransformation, [status(thm)], [f_225])).
% 3.77/1.65  tff(c_294, plain, (![F_594]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_594, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_594) | ~v3_pre_topc(F_594, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_594, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_185, c_292])).
% 3.77/1.65  tff(c_297, plain, (![F_594]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_594, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_594) | ~v3_pre_topc(F_594, '#skF_4') | ~m1_subset_1(F_594, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_56, c_52, c_50, c_48, c_46, c_42, c_40, c_81, c_294])).
% 3.77/1.65  tff(c_299, plain, (![F_595]: (~r1_tarski(F_595, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_595) | ~v3_pre_topc(F_595, '#skF_4') | ~m1_subset_1(F_595, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_58, c_54, c_136, c_297])).
% 3.77/1.65  tff(c_307, plain, (![B_28]: (~r1_tarski(u1_struct_0(B_28), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_28)) | ~v3_pre_topc(u1_struct_0(B_28), '#skF_4') | ~m1_pre_topc(B_28, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_299])).
% 3.77/1.65  tff(c_315, plain, (![B_596]: (~r1_tarski(u1_struct_0(B_596), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_596)) | ~v3_pre_topc(u1_struct_0(B_596), '#skF_4') | ~m1_pre_topc(B_596, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_307])).
% 3.77/1.65  tff(c_319, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_315])).
% 3.77/1.65  tff(c_322, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_319])).
% 3.77/1.65  tff(c_323, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_322])).
% 3.77/1.65  tff(c_327, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_279, c_323])).
% 3.77/1.65  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_42, c_127, c_44, c_327])).
% 3.77/1.65  tff(c_332, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_322])).
% 3.77/1.65  tff(c_342, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_332])).
% 3.77/1.65  tff(c_345, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_342])).
% 3.77/1.65  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_345])).
% 3.77/1.65  tff(c_349, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 3.77/1.65  tff(c_499, plain, (![C_633, D_634, G_638, A_636, E_637, B_635]: (r1_tmap_1(D_634, B_635, k3_tmap_1(A_636, B_635, C_633, D_634, E_637), G_638) | ~r1_tmap_1(C_633, B_635, E_637, G_638) | ~m1_pre_topc(D_634, C_633) | ~m1_subset_1(G_638, u1_struct_0(D_634)) | ~m1_subset_1(G_638, u1_struct_0(C_633)) | ~m1_subset_1(E_637, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_633), u1_struct_0(B_635)))) | ~v1_funct_2(E_637, u1_struct_0(C_633), u1_struct_0(B_635)) | ~v1_funct_1(E_637) | ~m1_pre_topc(D_634, A_636) | v2_struct_0(D_634) | ~m1_pre_topc(C_633, A_636) | v2_struct_0(C_633) | ~l1_pre_topc(B_635) | ~v2_pre_topc(B_635) | v2_struct_0(B_635) | ~l1_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.77/1.65  tff(c_501, plain, (![D_634, A_636, G_638]: (r1_tmap_1(D_634, '#skF_2', k3_tmap_1(A_636, '#skF_2', '#skF_4', D_634, '#skF_5'), G_638) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_638) | ~m1_pre_topc(D_634, '#skF_4') | ~m1_subset_1(G_638, u1_struct_0(D_634)) | ~m1_subset_1(G_638, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_634, A_636) | v2_struct_0(D_634) | ~m1_pre_topc('#skF_4', A_636) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636))), inference(resolution, [status(thm)], [c_46, c_499])).
% 3.77/1.65  tff(c_504, plain, (![D_634, A_636, G_638]: (r1_tmap_1(D_634, '#skF_2', k3_tmap_1(A_636, '#skF_2', '#skF_4', D_634, '#skF_5'), G_638) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_638) | ~m1_pre_topc(D_634, '#skF_4') | ~m1_subset_1(G_638, u1_struct_0(D_634)) | ~m1_subset_1(G_638, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_634, A_636) | v2_struct_0(D_634) | ~m1_pre_topc('#skF_4', A_636) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_48, c_501])).
% 3.77/1.65  tff(c_506, plain, (![D_639, A_640, G_641]: (r1_tmap_1(D_639, '#skF_2', k3_tmap_1(A_640, '#skF_2', '#skF_4', D_639, '#skF_5'), G_641) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_641) | ~m1_pre_topc(D_639, '#skF_4') | ~m1_subset_1(G_641, u1_struct_0(D_639)) | ~m1_subset_1(G_641, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_639, A_640) | v2_struct_0(D_639) | ~m1_pre_topc('#skF_4', A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(negUnitSimplification, [status(thm)], [c_64, c_54, c_504])).
% 3.77/1.65  tff(c_348, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 3.77/1.65  tff(c_509, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_506, c_348])).
% 3.77/1.65  tff(c_512, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_52, c_56, c_40, c_81, c_42, c_349, c_509])).
% 3.77/1.65  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_58, c_512])).
% 3.77/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.65  
% 3.77/1.65  Inference rules
% 3.77/1.65  ----------------------
% 3.77/1.65  #Ref     : 0
% 3.77/1.65  #Sup     : 77
% 3.77/1.65  #Fact    : 0
% 3.77/1.65  #Define  : 0
% 3.77/1.65  #Split   : 4
% 3.77/1.65  #Chain   : 0
% 3.77/1.65  #Close   : 0
% 3.77/1.65  
% 3.77/1.65  Ordering : KBO
% 3.77/1.65  
% 3.77/1.65  Simplification rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Subsume      : 17
% 3.77/1.66  #Demod        : 150
% 3.77/1.66  #Tautology    : 33
% 3.77/1.66  #SimpNegUnit  : 12
% 3.77/1.66  #BackRed      : 0
% 3.77/1.66  
% 3.77/1.66  #Partial instantiations: 0
% 3.77/1.66  #Strategies tried      : 1
% 3.77/1.66  
% 3.77/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.45
% 3.77/1.66  Parsing              : 0.23
% 3.77/1.66  CNF conversion       : 0.07
% 3.77/1.66  Main loop            : 0.35
% 3.77/1.66  Inferencing          : 0.12
% 3.77/1.66  Reduction            : 0.11
% 3.77/1.66  Demodulation         : 0.08
% 3.77/1.66  BG Simplification    : 0.02
% 3.77/1.66  Subsumption          : 0.07
% 3.77/1.66  Abstraction          : 0.01
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.66  Cooper               : 0.00
% 3.77/1.66  Total                : 0.85
% 3.77/1.66  Index Insertion      : 0.00
% 3.77/1.66  Index Deletion       : 0.00
% 3.77/1.66  Index Matching       : 0.00
% 3.77/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
