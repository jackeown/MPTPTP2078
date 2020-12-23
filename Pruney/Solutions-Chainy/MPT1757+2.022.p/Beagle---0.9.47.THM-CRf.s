%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 245 expanded)
%              Number of leaves         :   37 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 (1612 expanded)
%              Number of equality atoms :    6 (  87 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_213,negated_conjecture,(
    ~ ! [A] :
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
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_74,axiom,(
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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_121,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_30,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_77,plain,(
    ! [B_269,A_270] :
      ( l1_pre_topc(B_269)
      | ~ m1_pre_topc(B_269,A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_83,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_38,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_22,plain,(
    ! [B_19,A_17] :
      ( m1_subset_1(u1_struct_0(B_19),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_96,plain,(
    ! [B_278,A_279] :
      ( v3_pre_topc(u1_struct_0(B_278),A_279)
      | ~ v1_tsep_1(B_278,A_279)
      | ~ m1_subset_1(u1_struct_0(B_278),k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ m1_pre_topc(B_278,A_279)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_100,plain,(
    ! [B_19,A_17] :
      ( v3_pre_topc(u1_struct_0(B_19),A_17)
      | ~ v1_tsep_1(B_19,A_17)
      | ~ v2_pre_topc(A_17)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_69,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_60])).

tff(c_94,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_67,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_95,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_67])).

tff(c_120,plain,(
    ! [D_296,C_293,E_298,G_294,A_297,B_295] :
      ( r1_tmap_1(B_295,A_297,C_293,G_294)
      | ~ r1_tmap_1(D_296,A_297,k2_tmap_1(B_295,A_297,C_293,D_296),G_294)
      | ~ r1_tarski(E_298,u1_struct_0(D_296))
      | ~ r2_hidden(G_294,E_298)
      | ~ v3_pre_topc(E_298,B_295)
      | ~ m1_subset_1(G_294,u1_struct_0(D_296))
      | ~ m1_subset_1(G_294,u1_struct_0(B_295))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0(B_295)))
      | ~ m1_pre_topc(D_296,B_295)
      | v2_struct_0(D_296)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_295),u1_struct_0(A_297))))
      | ~ v1_funct_2(C_293,u1_struct_0(B_295),u1_struct_0(A_297))
      | ~ v1_funct_1(C_293)
      | ~ l1_pre_topc(B_295)
      | ~ v2_pre_topc(B_295)
      | v2_struct_0(B_295)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,(
    ! [E_298] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_298,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_298)
      | ~ v3_pre_topc(E_298,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_95,c_120])).

tff(c_131,plain,(
    ! [E_298] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_298,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_298)
      | ~ v3_pre_topc(E_298,'#skF_2')
      | ~ m1_subset_1(E_298,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_42,c_36,c_68,c_32,c_124])).

tff(c_133,plain,(
    ! [E_299] :
      ( ~ r1_tarski(E_299,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_299)
      | ~ v3_pre_topc(E_299,'#skF_2')
      | ~ m1_subset_1(E_299,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_40,c_94,c_131])).

tff(c_137,plain,(
    ! [B_19] :
      ( ~ r1_tarski(u1_struct_0(B_19),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_19))
      | ~ v3_pre_topc(u1_struct_0(B_19),'#skF_2')
      | ~ m1_pre_topc(B_19,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_141,plain,(
    ! [B_300] :
      ( ~ r1_tarski(u1_struct_0(B_300),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_300))
      | ~ v3_pre_topc(u1_struct_0(B_300),'#skF_2')
      | ~ m1_pre_topc(B_300,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_137])).

tff(c_145,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_148,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_145])).

tff(c_149,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_50,c_38,c_152])).

tff(c_157,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_167,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_170,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_14])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_173])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_179])).

tff(c_185,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_204,plain,(
    ! [A_312,B_309,D_311,C_313,F_310] :
      ( r1_tmap_1(D_311,A_312,k2_tmap_1(B_309,A_312,C_313,D_311),F_310)
      | ~ r1_tmap_1(B_309,A_312,C_313,F_310)
      | ~ m1_subset_1(F_310,u1_struct_0(D_311))
      | ~ m1_subset_1(F_310,u1_struct_0(B_309))
      | ~ m1_pre_topc(D_311,B_309)
      | v2_struct_0(D_311)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_309),u1_struct_0(A_312))))
      | ~ v1_funct_2(C_313,u1_struct_0(B_309),u1_struct_0(A_312))
      | ~ v1_funct_1(C_313)
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_206,plain,(
    ! [D_311,F_310] :
      ( r1_tmap_1(D_311,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_311),F_310)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_310)
      | ~ m1_subset_1(F_310,u1_struct_0(D_311))
      | ~ m1_subset_1(F_310,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_311,'#skF_2')
      | v2_struct_0(D_311)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_209,plain,(
    ! [D_311,F_310] :
      ( r1_tmap_1(D_311,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_311),F_310)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_310)
      | ~ m1_subset_1(F_310,u1_struct_0(D_311))
      | ~ m1_subset_1(F_310,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_311,'#skF_2')
      | v2_struct_0(D_311)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_206])).

tff(c_211,plain,(
    ! [D_314,F_315] :
      ( r1_tmap_1(D_314,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_314),F_315)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_315)
      | ~ m1_subset_1(F_315,u1_struct_0(D_314))
      | ~ m1_subset_1(F_315,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_314,'#skF_2')
      | v2_struct_0(D_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_209])).

tff(c_184,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_214,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_211,c_184])).

tff(c_217,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68,c_32,c_185,c_214])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.40  
% 2.73/1.40  %Foreground sorts:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Background operators:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Foreground operators:
% 2.73/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.40  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.73/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.40  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.73/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.73/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.73/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.40  
% 2.73/1.43  tff(f_213, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 2.73/1.43  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.73/1.43  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.43  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.43  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.73/1.43  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 2.73/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.43  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 2.73/1.43  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.73/1.43  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 2.73/1.43  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_30, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_68, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 2.73/1.43  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_77, plain, (![B_269, A_270]: (l1_pre_topc(B_269) | ~m1_pre_topc(B_269, A_270) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.43  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_77])).
% 2.73/1.43  tff(c_83, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80])).
% 2.73/1.43  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.43  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.43  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_38, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_22, plain, (![B_19, A_17]: (m1_subset_1(u1_struct_0(B_19), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.43  tff(c_96, plain, (![B_278, A_279]: (v3_pre_topc(u1_struct_0(B_278), A_279) | ~v1_tsep_1(B_278, A_279) | ~m1_subset_1(u1_struct_0(B_278), k1_zfmisc_1(u1_struct_0(A_279))) | ~m1_pre_topc(B_278, A_279) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.43  tff(c_100, plain, (![B_19, A_17]: (v3_pre_topc(u1_struct_0(B_19), A_17) | ~v1_tsep_1(B_19, A_17) | ~v2_pre_topc(A_17) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.73/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.43  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_60, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_69, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_60])).
% 2.73/1.43  tff(c_94, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 2.73/1.43  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_66, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.73/1.43  tff(c_67, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 2.73/1.43  tff(c_95, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_94, c_67])).
% 2.73/1.43  tff(c_120, plain, (![D_296, C_293, E_298, G_294, A_297, B_295]: (r1_tmap_1(B_295, A_297, C_293, G_294) | ~r1_tmap_1(D_296, A_297, k2_tmap_1(B_295, A_297, C_293, D_296), G_294) | ~r1_tarski(E_298, u1_struct_0(D_296)) | ~r2_hidden(G_294, E_298) | ~v3_pre_topc(E_298, B_295) | ~m1_subset_1(G_294, u1_struct_0(D_296)) | ~m1_subset_1(G_294, u1_struct_0(B_295)) | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0(B_295))) | ~m1_pre_topc(D_296, B_295) | v2_struct_0(D_296) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_295), u1_struct_0(A_297)))) | ~v1_funct_2(C_293, u1_struct_0(B_295), u1_struct_0(A_297)) | ~v1_funct_1(C_293) | ~l1_pre_topc(B_295) | ~v2_pre_topc(B_295) | v2_struct_0(B_295) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.73/1.43  tff(c_124, plain, (![E_298]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_298, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_298) | ~v3_pre_topc(E_298, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_95, c_120])).
% 2.73/1.43  tff(c_131, plain, (![E_298]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_298, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_298) | ~v3_pre_topc(E_298, '#skF_2') | ~m1_subset_1(E_298, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_42, c_36, c_68, c_32, c_124])).
% 2.73/1.43  tff(c_133, plain, (![E_299]: (~r1_tarski(E_299, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_299) | ~v3_pre_topc(E_299, '#skF_2') | ~m1_subset_1(E_299, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_40, c_94, c_131])).
% 2.73/1.43  tff(c_137, plain, (![B_19]: (~r1_tarski(u1_struct_0(B_19), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_19)) | ~v3_pre_topc(u1_struct_0(B_19), '#skF_2') | ~m1_pre_topc(B_19, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.73/1.43  tff(c_141, plain, (![B_300]: (~r1_tarski(u1_struct_0(B_300), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_300)) | ~v3_pre_topc(u1_struct_0(B_300), '#skF_2') | ~m1_pre_topc(B_300, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_137])).
% 2.73/1.43  tff(c_145, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_141])).
% 2.73/1.43  tff(c_148, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_145])).
% 2.73/1.43  tff(c_149, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_148])).
% 2.73/1.43  tff(c_152, plain, (~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_100, c_149])).
% 2.73/1.43  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_50, c_38, c_152])).
% 2.73/1.43  tff(c_157, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_148])).
% 2.73/1.43  tff(c_167, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_157])).
% 2.73/1.43  tff(c_170, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 2.73/1.43  tff(c_14, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.43  tff(c_173, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_170, c_14])).
% 2.73/1.43  tff(c_176, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_173])).
% 2.73/1.43  tff(c_179, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_176])).
% 2.73/1.43  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_179])).
% 2.73/1.43  tff(c_185, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 2.73/1.43  tff(c_204, plain, (![A_312, B_309, D_311, C_313, F_310]: (r1_tmap_1(D_311, A_312, k2_tmap_1(B_309, A_312, C_313, D_311), F_310) | ~r1_tmap_1(B_309, A_312, C_313, F_310) | ~m1_subset_1(F_310, u1_struct_0(D_311)) | ~m1_subset_1(F_310, u1_struct_0(B_309)) | ~m1_pre_topc(D_311, B_309) | v2_struct_0(D_311) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_309), u1_struct_0(A_312)))) | ~v1_funct_2(C_313, u1_struct_0(B_309), u1_struct_0(A_312)) | ~v1_funct_1(C_313) | ~l1_pre_topc(B_309) | ~v2_pre_topc(B_309) | v2_struct_0(B_309) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312) | v2_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.73/1.43  tff(c_206, plain, (![D_311, F_310]: (r1_tmap_1(D_311, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_311), F_310) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_310) | ~m1_subset_1(F_310, u1_struct_0(D_311)) | ~m1_subset_1(F_310, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_311, '#skF_2') | v2_struct_0(D_311) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_204])).
% 2.73/1.43  tff(c_209, plain, (![D_311, F_310]: (r1_tmap_1(D_311, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_311), F_310) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_310) | ~m1_subset_1(F_310, u1_struct_0(D_311)) | ~m1_subset_1(F_310, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_311, '#skF_2') | v2_struct_0(D_311) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_206])).
% 2.73/1.43  tff(c_211, plain, (![D_314, F_315]: (r1_tmap_1(D_314, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_314), F_315) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_315) | ~m1_subset_1(F_315, u1_struct_0(D_314)) | ~m1_subset_1(F_315, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_314, '#skF_2') | v2_struct_0(D_314))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_209])).
% 2.73/1.43  tff(c_184, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 2.73/1.43  tff(c_214, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_211, c_184])).
% 2.73/1.43  tff(c_217, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68, c_32, c_185, c_214])).
% 2.73/1.43  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_217])).
% 2.73/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  Inference rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Ref     : 0
% 2.73/1.43  #Sup     : 22
% 2.73/1.43  #Fact    : 0
% 2.73/1.43  #Define  : 0
% 2.73/1.43  #Split   : 2
% 2.73/1.43  #Chain   : 0
% 2.73/1.43  #Close   : 0
% 2.73/1.43  
% 2.73/1.43  Ordering : KBO
% 2.73/1.43  
% 2.73/1.43  Simplification rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Subsume      : 5
% 2.73/1.43  #Demod        : 52
% 2.73/1.43  #Tautology    : 12
% 2.73/1.43  #SimpNegUnit  : 8
% 2.73/1.43  #BackRed      : 0
% 2.73/1.43  
% 2.73/1.43  #Partial instantiations: 0
% 2.73/1.43  #Strategies tried      : 1
% 2.73/1.43  
% 2.73/1.43  Timing (in seconds)
% 2.73/1.43  ----------------------
% 2.73/1.43  Preprocessing        : 0.39
% 2.73/1.43  Parsing              : 0.20
% 2.73/1.43  CNF conversion       : 0.05
% 2.73/1.43  Main loop            : 0.24
% 2.73/1.43  Inferencing          : 0.08
% 2.73/1.43  Reduction            : 0.08
% 2.73/1.43  Demodulation         : 0.06
% 2.73/1.43  BG Simplification    : 0.02
% 2.73/1.43  Subsumption          : 0.04
% 2.73/1.43  Abstraction          : 0.01
% 2.73/1.43  MUC search           : 0.00
% 2.73/1.43  Cooper               : 0.00
% 2.73/1.43  Total                : 0.68
% 2.73/1.43  Index Insertion      : 0.00
% 2.73/1.43  Index Deletion       : 0.00
% 2.73/1.43  Index Matching       : 0.00
% 2.73/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
