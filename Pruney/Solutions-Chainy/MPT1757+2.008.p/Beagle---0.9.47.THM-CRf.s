%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:05 EST 2020

% Result     : Theorem 10.27s
% Output     : CNFRefutation 10.44s
% Verified   : 
% Statistics : Number of formulae       :  180 (3004 expanded)
%              Number of leaves         :   41 (1146 expanded)
%              Depth                    :   52
%              Number of atoms          :  761 (22564 expanded)
%              Number of equality atoms :    6 (1036 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_289,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_159,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_246,axiom,(
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
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_152,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_199,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_48,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_86,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_40,plain,(
    ! [B_63,A_61] :
      ( m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_243,plain,(
    ! [A_365,B_366,C_367] :
      ( r1_tarski('#skF_2'(A_365,B_366,C_367),C_367)
      | ~ m1_connsp_2(C_367,A_365,B_366)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ m1_subset_1(B_366,u1_struct_0(A_365))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_252,plain,(
    ! [A_61,B_366,B_63] :
      ( r1_tarski('#skF_2'(A_61,B_366,u1_struct_0(B_63)),u1_struct_0(B_63))
      | ~ m1_connsp_2(u1_struct_0(B_63),A_61,B_366)
      | ~ m1_subset_1(B_366,u1_struct_0(A_61))
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_40,c_243])).

tff(c_32,plain,(
    ! [A_32,B_44,C_50] :
      ( m1_subset_1('#skF_2'(A_32,B_44,C_50),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_connsp_2(C_50,A_32,B_44)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_87,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78])).

tff(c_133,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_85,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_139,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_85])).

tff(c_340,plain,(
    ! [B_431,A_432,C_427,E_430,D_429,G_428] :
      ( r1_tmap_1(B_431,A_432,C_427,G_428)
      | ~ r1_tmap_1(D_429,A_432,k2_tmap_1(B_431,A_432,C_427,D_429),G_428)
      | ~ m1_connsp_2(E_430,B_431,G_428)
      | ~ r1_tarski(E_430,u1_struct_0(D_429))
      | ~ m1_subset_1(G_428,u1_struct_0(D_429))
      | ~ m1_subset_1(G_428,u1_struct_0(B_431))
      | ~ m1_subset_1(E_430,k1_zfmisc_1(u1_struct_0(B_431)))
      | ~ m1_pre_topc(D_429,B_431)
      | v2_struct_0(D_429)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_431),u1_struct_0(A_432))))
      | ~ v1_funct_2(C_427,u1_struct_0(B_431),u1_struct_0(A_432))
      | ~ v1_funct_1(C_427)
      | ~ l1_pre_topc(B_431)
      | ~ v2_pre_topc(B_431)
      | v2_struct_0(B_431)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_344,plain,(
    ! [E_430] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_430,'#skF_4','#skF_8')
      | ~ r1_tarski(E_430,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_430,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139,c_340])).

tff(c_351,plain,(
    ! [E_430] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_430,'#skF_4','#skF_8')
      | ~ r1_tarski(E_430,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_430,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_62,c_60,c_54,c_86,c_50,c_344])).

tff(c_353,plain,(
    ! [E_433] :
      ( ~ m1_connsp_2(E_433,'#skF_4','#skF_8')
      | ~ r1_tarski(E_433,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_433,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_58,c_133,c_351])).

tff(c_357,plain,(
    ! [B_44,C_50] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_44,C_50),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_44,C_50),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_50,'#skF_4',B_44)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_353])).

tff(c_372,plain,(
    ! [B_44,C_50] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_44,C_50),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_44,C_50),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_50,'#skF_4',B_44)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_357])).

tff(c_484,plain,(
    ! [B_445,C_446] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_445,C_446),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_445,C_446),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_446,'#skF_4',B_445)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_372])).

tff(c_488,plain,(
    ! [B_366] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_366,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_366)
      | ~ m1_subset_1(B_366,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_252,c_484])).

tff(c_495,plain,(
    ! [B_366] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_366,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_366)
      | ~ m1_subset_1(B_366,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_68,c_488])).

tff(c_496,plain,(
    ! [B_366] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_366,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_366)
      | ~ m1_subset_1(B_366,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_495])).

tff(c_501,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_504,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_501])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_504])).

tff(c_513,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_56,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_214,plain,(
    ! [B_350,A_351] :
      ( v3_pre_topc(u1_struct_0(B_350),A_351)
      | ~ v1_tsep_1(B_350,A_351)
      | ~ m1_subset_1(u1_struct_0(B_350),k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ m1_pre_topc(B_350,A_351)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_221,plain,(
    ! [B_63,A_61] :
      ( v3_pre_topc(u1_struct_0(B_63),A_61)
      | ~ v1_tsep_1(B_63,A_61)
      | ~ v2_pre_topc(A_61)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_121,plain,(
    ! [B_320,A_321] :
      ( v2_pre_topc(B_320)
      | ~ m1_pre_topc(B_320,A_321)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_127,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_124])).

tff(c_94,plain,(
    ! [B_312,A_313] :
      ( l1_pre_topc(B_312)
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_97])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_32,B_44,C_50] :
      ( r1_tarski('#skF_2'(A_32,B_44,C_50),C_50)
      | ~ m1_connsp_2(C_50,A_32,B_44)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_522,plain,(
    ! [B_44] :
      ( r1_tarski('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_513,c_28])).

tff(c_539,plain,(
    ! [B_44] :
      ( r1_tarski('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_522])).

tff(c_540,plain,(
    ! [B_44] :
      ( r1_tarski('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_539])).

tff(c_26,plain,(
    ! [B_44,A_32,C_50] :
      ( r2_hidden(B_44,'#skF_2'(A_32,B_44,C_50))
      | ~ m1_connsp_2(C_50,A_32,B_44)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_518,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_513,c_26])).

tff(c_531,plain,(
    ! [B_44] :
      ( r2_hidden(B_44,'#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_518])).

tff(c_547,plain,(
    ! [B_451] :
      ( r2_hidden(B_451,'#skF_2'('#skF_4',B_451,u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_451)
      | ~ m1_subset_1(B_451,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_531])).

tff(c_24,plain,(
    ! [C_50,A_32,B_44,D_53] :
      ( m1_connsp_2(C_50,A_32,B_44)
      | ~ r2_hidden(B_44,D_53)
      | ~ r1_tarski(D_53,C_50)
      | ~ v3_pre_topc(D_53,A_32)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_626,plain,(
    ! [C_476,A_477,B_478] :
      ( m1_connsp_2(C_476,A_477,B_478)
      | ~ r1_tarski('#skF_2'('#skF_4',B_478,u1_struct_0('#skF_6')),C_476)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_478,u1_struct_0('#skF_6')),A_477)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_478,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0(A_477)))
      | ~ m1_subset_1(C_476,k1_zfmisc_1(u1_struct_0(A_477)))
      | ~ m1_subset_1(B_478,u1_struct_0(A_477))
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_478)
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_547,c_24])).

tff(c_917,plain,(
    ! [B_532,A_533] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_532,u1_struct_0('#skF_6')),A_533,B_532)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_532,u1_struct_0('#skF_6')),A_533)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_532,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0(A_533)))
      | ~ m1_subset_1(B_532,u1_struct_0(A_533))
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_532)
      | ~ m1_subset_1(B_532,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_626])).

tff(c_1063,plain,(
    ! [B_547,A_548] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_547,u1_struct_0('#skF_6')),A_548,B_547)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_547,u1_struct_0('#skF_6')),A_548)
      | ~ m1_subset_1(B_547,u1_struct_0(A_548))
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_547)
      | ~ m1_subset_1(B_547,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_2'('#skF_4',B_547,u1_struct_0('#skF_6')),u1_struct_0(A_548)) ) ),
    inference(resolution,[status(thm)],[c_10,c_917])).

tff(c_1067,plain,(
    ! [B_44] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),'#skF_6',B_44)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_540,c_1063])).

tff(c_1083,plain,(
    ! [B_44] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),'#skF_6',B_44)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_1067])).

tff(c_1097,plain,(
    ! [B_549] :
      ( m1_connsp_2('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),'#skF_6',B_549)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_549)
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1083])).

tff(c_18,plain,(
    ! [C_21,A_18,B_19] :
      ( m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_connsp_2(C_21,A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1101,plain,(
    ! [B_549] :
      ( m1_subset_1('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_549)
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1097,c_18])).

tff(c_1108,plain,(
    ! [B_549] :
      ( m1_subset_1('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_549,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_549)
      | ~ m1_subset_1(B_549,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_1101])).

tff(c_1110,plain,(
    ! [B_550] :
      ( m1_subset_1('#skF_2'('#skF_4',B_550,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_550,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_550)
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1108])).

tff(c_128,plain,(
    ! [B_322,A_323] :
      ( m1_subset_1(u1_struct_0(B_322),k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ m1_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [B_322,A_323] :
      ( r1_tarski(u1_struct_0(B_322),u1_struct_0(A_323))
      | ~ m1_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323) ) ),
    inference(resolution,[status(thm)],[c_128,c_8])).

tff(c_382,plain,(
    ! [A_434] :
      ( ~ m1_connsp_2(A_434,'#skF_4','#skF_8')
      | ~ r1_tarski(A_434,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_434,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_353])).

tff(c_420,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_421,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_425,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_421])).

tff(c_429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_425])).

tff(c_431,plain,(
    r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_270,plain,(
    ! [B_377,A_378,C_379] :
      ( r2_hidden(B_377,'#skF_2'(A_378,B_377,C_379))
      | ~ m1_connsp_2(C_379,A_378,B_377)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_subset_1(B_377,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_280,plain,(
    ! [B_377,A_378,A_3] :
      ( r2_hidden(B_377,'#skF_2'(A_378,B_377,A_3))
      | ~ m1_connsp_2(A_3,A_378,B_377)
      | ~ m1_subset_1(B_377,u1_struct_0(A_378))
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ r1_tarski(A_3,u1_struct_0(A_378)) ) ),
    inference(resolution,[status(thm)],[c_10,c_270])).

tff(c_302,plain,(
    ! [C_395,A_396,B_397,D_398] :
      ( m1_connsp_2(C_395,A_396,B_397)
      | ~ r2_hidden(B_397,D_398)
      | ~ r1_tarski(D_398,C_395)
      | ~ v3_pre_topc(D_398,A_396)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ m1_subset_1(C_395,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ m1_subset_1(B_397,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_839,plain,(
    ! [A_517,A_516,B_519,C_520,A_518] :
      ( m1_connsp_2(C_520,A_516,B_519)
      | ~ r1_tarski('#skF_2'(A_518,B_519,A_517),C_520)
      | ~ v3_pre_topc('#skF_2'(A_518,B_519,A_517),A_516)
      | ~ m1_subset_1('#skF_2'(A_518,B_519,A_517),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(C_520,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(B_519,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516)
      | ~ m1_connsp_2(A_517,A_518,B_519)
      | ~ m1_subset_1(B_519,u1_struct_0(A_518))
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518)
      | ~ r1_tarski(A_517,u1_struct_0(A_518)) ) ),
    inference(resolution,[status(thm)],[c_280,c_302])).

tff(c_845,plain,(
    ! [A_516,B_44] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),A_516,B_44)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),A_516)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_540,c_839])).

tff(c_864,plain,(
    ! [A_516,B_44] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),A_516,B_44)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),A_516)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516)
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_68,c_66,c_845])).

tff(c_865,plain,(
    ! [A_516,B_44] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),A_516,B_44)
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),A_516)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_44,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ m1_subset_1(B_44,u1_struct_0(A_516))
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516)
      | v2_struct_0(A_516)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_44)
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_864])).

tff(c_1115,plain,(
    ! [B_550] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_550)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_550,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_550)
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1110,c_865])).

tff(c_1134,plain,(
    ! [B_550] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_550)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_550,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_550)
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_1115])).

tff(c_1135,plain,(
    ! [B_550] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_550)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_550,u1_struct_0('#skF_6')),'#skF_6')
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_550)
      | ~ m1_subset_1(B_550,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1134])).

tff(c_1154,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1135])).

tff(c_1160,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_1154])).

tff(c_1167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1160])).

tff(c_1169,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1135])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( m1_connsp_2('#skF_1'(A_22,B_23),A_22,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_192,plain,(
    ! [C_341,A_342,B_343] :
      ( m1_subset_1(C_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_connsp_2(C_341,A_342,B_343)
      | ~ m1_subset_1(B_343,u1_struct_0(A_342))
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_196,plain,(
    ! [A_344,B_345] :
      ( m1_subset_1('#skF_1'(A_344,B_345),k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ m1_subset_1(B_345,u1_struct_0(A_344))
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_20,c_192])).

tff(c_200,plain,(
    ! [A_344,B_345] :
      ( r1_tarski('#skF_1'(A_344,B_345),u1_struct_0(A_344))
      | ~ m1_subset_1(B_345,u1_struct_0(A_344))
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(resolution,[status(thm)],[c_196,c_8])).

tff(c_258,plain,(
    ! [A_371,B_372,C_373] :
      ( v3_pre_topc('#skF_2'(A_371,B_372,C_373),A_371)
      | ~ m1_connsp_2(C_373,A_371,B_372)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(u1_struct_0(A_371)))
      | ~ m1_subset_1(B_372,u1_struct_0(A_371))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_268,plain,(
    ! [A_371,B_372,A_3] :
      ( v3_pre_topc('#skF_2'(A_371,B_372,A_3),A_371)
      | ~ m1_connsp_2(A_3,A_371,B_372)
      | ~ m1_subset_1(B_372,u1_struct_0(A_371))
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371)
      | ~ r1_tarski(A_3,u1_struct_0(A_371)) ) ),
    inference(resolution,[status(thm)],[c_10,c_258])).

tff(c_288,plain,(
    ! [A_392,B_393,C_394] :
      ( m1_subset_1('#skF_2'(A_392,B_393,C_394),k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ m1_connsp_2(C_394,A_392,B_393)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ m1_subset_1(B_393,u1_struct_0(A_392))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_301,plain,(
    ! [A_392,B_393,C_394] :
      ( r1_tarski('#skF_2'(A_392,B_393,C_394),u1_struct_0(A_392))
      | ~ m1_connsp_2(C_394,A_392,B_393)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ m1_subset_1(B_393,u1_struct_0(A_392))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_288,c_8])).

tff(c_2404,plain,(
    ! [A_697,A_698,B_699,C_700] :
      ( m1_connsp_2(u1_struct_0(A_697),A_698,B_699)
      | ~ v3_pre_topc('#skF_2'(A_697,B_699,C_700),A_698)
      | ~ m1_subset_1('#skF_2'(A_697,B_699,C_700),k1_zfmisc_1(u1_struct_0(A_698)))
      | ~ m1_subset_1(u1_struct_0(A_697),k1_zfmisc_1(u1_struct_0(A_698)))
      | ~ m1_subset_1(B_699,u1_struct_0(A_698))
      | ~ l1_pre_topc(A_698)
      | ~ v2_pre_topc(A_698)
      | v2_struct_0(A_698)
      | ~ r1_tarski(C_700,u1_struct_0(A_697))
      | ~ m1_connsp_2(C_700,A_697,B_699)
      | ~ m1_subset_1(C_700,k1_zfmisc_1(u1_struct_0(A_697)))
      | ~ m1_subset_1(B_699,u1_struct_0(A_697))
      | ~ l1_pre_topc(A_697)
      | ~ v2_pre_topc(A_697)
      | v2_struct_0(A_697) ) ),
    inference(resolution,[status(thm)],[c_301,c_839])).

tff(c_2445,plain,(
    ! [A_701,B_702,C_703] :
      ( m1_connsp_2(u1_struct_0(A_701),A_701,B_702)
      | ~ v3_pre_topc('#skF_2'(A_701,B_702,C_703),A_701)
      | ~ m1_subset_1(u1_struct_0(A_701),k1_zfmisc_1(u1_struct_0(A_701)))
      | ~ r1_tarski(C_703,u1_struct_0(A_701))
      | ~ m1_connsp_2(C_703,A_701,B_702)
      | ~ m1_subset_1(C_703,k1_zfmisc_1(u1_struct_0(A_701)))
      | ~ m1_subset_1(B_702,u1_struct_0(A_701))
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(resolution,[status(thm)],[c_32,c_2404])).

tff(c_2506,plain,(
    ! [A_704,B_705,A_706] :
      ( m1_connsp_2(u1_struct_0(A_704),A_704,B_705)
      | ~ m1_subset_1(u1_struct_0(A_704),k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_subset_1(A_706,k1_zfmisc_1(u1_struct_0(A_704)))
      | ~ m1_connsp_2(A_706,A_704,B_705)
      | ~ m1_subset_1(B_705,u1_struct_0(A_704))
      | ~ l1_pre_topc(A_704)
      | ~ v2_pre_topc(A_704)
      | v2_struct_0(A_704)
      | ~ r1_tarski(A_706,u1_struct_0(A_704)) ) ),
    inference(resolution,[status(thm)],[c_268,c_2445])).

tff(c_2508,plain,(
    ! [B_705,A_706] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_705)
      | ~ m1_subset_1(A_706,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_706,'#skF_6',B_705)
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_706,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1169,c_2506])).

tff(c_2519,plain,(
    ! [B_705,A_706] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_705)
      | ~ m1_subset_1(A_706,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_706,'#skF_6',B_705)
      | ~ m1_subset_1(B_705,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_706,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_2508])).

tff(c_2591,plain,(
    ! [B_709,A_710] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_709)
      | ~ m1_subset_1(A_710,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_710,'#skF_6',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_710,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2519])).

tff(c_2728,plain,(
    ! [B_716,A_717] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_716)
      | ~ m1_connsp_2(A_717,'#skF_6',B_716)
      | ~ m1_subset_1(B_716,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_717,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2591])).

tff(c_2749,plain,(
    ! [B_23] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_23)
      | ~ r1_tarski('#skF_1'('#skF_6',B_23),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_2728])).

tff(c_2773,plain,(
    ! [B_23] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_23)
      | ~ r1_tarski('#skF_1'('#skF_6',B_23),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_23,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_2749])).

tff(c_2775,plain,(
    ! [B_718] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_718)
      | ~ r1_tarski('#skF_1'('#skF_6',B_718),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_718,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2773])).

tff(c_2779,plain,(
    ! [B_345] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_345)
      | ~ m1_subset_1(B_345,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_200,c_2775])).

tff(c_2782,plain,(
    ! [B_345] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_345)
      | ~ m1_subset_1(B_345,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_2779])).

tff(c_2784,plain,(
    ! [B_719] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_6',B_719)
      | ~ m1_subset_1(B_719,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2782])).

tff(c_22,plain,(
    ! [C_31,B_29,A_25] :
      ( r2_hidden(C_31,B_29)
      | ~ m1_connsp_2(B_29,A_25,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_25))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2786,plain,(
    ! [B_719] :
      ( r2_hidden(B_719,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_719,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2784,c_22])).

tff(c_2791,plain,(
    ! [B_719] :
      ( r2_hidden(B_719,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1(B_719,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_100,c_1169,c_2786])).

tff(c_2797,plain,(
    ! [B_720] :
      ( r2_hidden(B_720,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_720,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2791])).

tff(c_3696,plain,(
    ! [C_821,A_822,B_823] :
      ( m1_connsp_2(C_821,A_822,B_823)
      | ~ r1_tarski(u1_struct_0('#skF_6'),C_821)
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),A_822)
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_822)))
      | ~ m1_subset_1(C_821,k1_zfmisc_1(u1_struct_0(A_822)))
      | ~ m1_subset_1(B_823,u1_struct_0(A_822))
      | ~ l1_pre_topc(A_822)
      | ~ v2_pre_topc(A_822)
      | v2_struct_0(A_822)
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2797,c_24])).

tff(c_3706,plain,(
    ! [C_821,B_823] :
      ( m1_connsp_2(C_821,'#skF_4',B_823)
      | ~ r1_tarski(u1_struct_0('#skF_6'),C_821)
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_513,c_3696])).

tff(c_3727,plain,(
    ! [C_821,B_823] :
      ( m1_connsp_2(C_821,'#skF_4',B_823)
      | ~ r1_tarski(u1_struct_0('#skF_6'),C_821)
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_3706])).

tff(c_3728,plain,(
    ! [C_821,B_823] :
      ( m1_connsp_2(C_821,'#skF_4',B_823)
      | ~ r1_tarski(u1_struct_0('#skF_6'),C_821)
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_823,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3727])).

tff(c_3754,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3728])).

tff(c_3757,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_3754])).

tff(c_3761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_68,c_56,c_3757])).

tff(c_3770,plain,(
    ! [C_829,B_830] :
      ( m1_connsp_2(C_829,'#skF_4',B_830)
      | ~ r1_tarski(u1_struct_0('#skF_6'),C_829)
      | ~ m1_subset_1(C_829,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_830,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_830,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_3728])).

tff(c_3799,plain,(
    ! [B_830] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_830)
      | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_6'))
      | ~ m1_subset_1(B_830,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_830,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_513,c_3770])).

tff(c_3860,plain,(
    ! [B_831] :
      ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_831)
      | ~ m1_subset_1(B_831,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_831,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3799])).

tff(c_430,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_3867,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3860,c_430])).

tff(c_3878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_86,c_3867])).

tff(c_3880,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4070,plain,(
    ! [B_922,D_920,C_921,F_919,A_923] :
      ( r1_tmap_1(D_920,A_923,k2_tmap_1(B_922,A_923,C_921,D_920),F_919)
      | ~ r1_tmap_1(B_922,A_923,C_921,F_919)
      | ~ m1_subset_1(F_919,u1_struct_0(D_920))
      | ~ m1_subset_1(F_919,u1_struct_0(B_922))
      | ~ m1_pre_topc(D_920,B_922)
      | v2_struct_0(D_920)
      | ~ m1_subset_1(C_921,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_922),u1_struct_0(A_923))))
      | ~ v1_funct_2(C_921,u1_struct_0(B_922),u1_struct_0(A_923))
      | ~ v1_funct_1(C_921)
      | ~ l1_pre_topc(B_922)
      | ~ v2_pre_topc(B_922)
      | v2_struct_0(B_922)
      | ~ l1_pre_topc(A_923)
      | ~ v2_pre_topc(A_923)
      | v2_struct_0(A_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4072,plain,(
    ! [D_920,F_919] :
      ( r1_tmap_1(D_920,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_920),F_919)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_919)
      | ~ m1_subset_1(F_919,u1_struct_0(D_920))
      | ~ m1_subset_1(F_919,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_920,'#skF_4')
      | v2_struct_0(D_920)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_60,c_4070])).

tff(c_4078,plain,(
    ! [D_920,F_919] :
      ( r1_tmap_1(D_920,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_920),F_919)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_919)
      | ~ m1_subset_1(F_919,u1_struct_0(D_920))
      | ~ m1_subset_1(F_919,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_920,'#skF_4')
      | v2_struct_0(D_920)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_62,c_4072])).

tff(c_4081,plain,(
    ! [D_924,F_925] :
      ( r1_tmap_1(D_924,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_924),F_925)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_925)
      | ~ m1_subset_1(F_925,u1_struct_0(D_924))
      | ~ m1_subset_1(F_925,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_924,'#skF_4')
      | v2_struct_0(D_924) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_4078])).

tff(c_3879,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4084,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4081,c_3879])).

tff(c_4087,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_86,c_50,c_3880,c_4084])).

tff(c_4089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4087])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.27/3.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.44/3.82  
% 10.44/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.44/3.82  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4 > #skF_1
% 10.44/3.82  
% 10.44/3.82  %Foreground sorts:
% 10.44/3.82  
% 10.44/3.82  
% 10.44/3.82  %Background operators:
% 10.44/3.82  
% 10.44/3.82  
% 10.44/3.82  %Foreground operators:
% 10.44/3.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.44/3.82  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 10.44/3.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.44/3.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.44/3.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.44/3.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.44/3.82  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 10.44/3.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.44/3.82  tff('#skF_7', type, '#skF_7': $i).
% 10.44/3.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.44/3.82  tff('#skF_5', type, '#skF_5': $i).
% 10.44/3.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.44/3.82  tff('#skF_6', type, '#skF_6': $i).
% 10.44/3.82  tff('#skF_3', type, '#skF_3': $i).
% 10.44/3.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.44/3.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.44/3.82  tff('#skF_8', type, '#skF_8': $i).
% 10.44/3.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.44/3.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.44/3.82  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 10.44/3.82  tff('#skF_4', type, '#skF_4': $i).
% 10.44/3.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.44/3.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.44/3.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.44/3.82  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.44/3.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.44/3.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.44/3.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.44/3.82  
% 10.44/3.86  tff(f_289, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 10.44/3.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.44/3.86  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.44/3.86  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 10.44/3.86  tff(f_246, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 10.44/3.86  tff(f_152, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 10.44/3.86  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 10.44/3.86  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.44/3.86  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.44/3.86  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 10.44/3.86  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 10.44/3.86  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 10.44/3.86  tff(f_199, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 10.44/3.86  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_48, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_86, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 10.44/3.86  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.44/3.86  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_40, plain, (![B_63, A_61]: (m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.44/3.86  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_243, plain, (![A_365, B_366, C_367]: (r1_tarski('#skF_2'(A_365, B_366, C_367), C_367) | ~m1_connsp_2(C_367, A_365, B_366) | ~m1_subset_1(C_367, k1_zfmisc_1(u1_struct_0(A_365))) | ~m1_subset_1(B_366, u1_struct_0(A_365)) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_252, plain, (![A_61, B_366, B_63]: (r1_tarski('#skF_2'(A_61, B_366, u1_struct_0(B_63)), u1_struct_0(B_63)) | ~m1_connsp_2(u1_struct_0(B_63), A_61, B_366) | ~m1_subset_1(B_366, u1_struct_0(A_61)) | ~v2_pre_topc(A_61) | v2_struct_0(A_61) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_40, c_243])).
% 10.44/3.86  tff(c_32, plain, (![A_32, B_44, C_50]: (m1_subset_1('#skF_2'(A_32, B_44, C_50), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_connsp_2(C_50, A_32, B_44) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_78, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_87, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_78])).
% 10.44/3.86  tff(c_133, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 10.44/3.86  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_84, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_85, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_84])).
% 10.44/3.86  tff(c_139, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_133, c_85])).
% 10.44/3.86  tff(c_340, plain, (![B_431, A_432, C_427, E_430, D_429, G_428]: (r1_tmap_1(B_431, A_432, C_427, G_428) | ~r1_tmap_1(D_429, A_432, k2_tmap_1(B_431, A_432, C_427, D_429), G_428) | ~m1_connsp_2(E_430, B_431, G_428) | ~r1_tarski(E_430, u1_struct_0(D_429)) | ~m1_subset_1(G_428, u1_struct_0(D_429)) | ~m1_subset_1(G_428, u1_struct_0(B_431)) | ~m1_subset_1(E_430, k1_zfmisc_1(u1_struct_0(B_431))) | ~m1_pre_topc(D_429, B_431) | v2_struct_0(D_429) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_431), u1_struct_0(A_432)))) | ~v1_funct_2(C_427, u1_struct_0(B_431), u1_struct_0(A_432)) | ~v1_funct_1(C_427) | ~l1_pre_topc(B_431) | ~v2_pre_topc(B_431) | v2_struct_0(B_431) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.44/3.86  tff(c_344, plain, (![E_430]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_430, '#skF_4', '#skF_8') | ~r1_tarski(E_430, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_430, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_340])).
% 10.44/3.86  tff(c_351, plain, (![E_430]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_430, '#skF_4', '#skF_8') | ~r1_tarski(E_430, u1_struct_0('#skF_6')) | ~m1_subset_1(E_430, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_62, c_60, c_54, c_86, c_50, c_344])).
% 10.44/3.86  tff(c_353, plain, (![E_433]: (~m1_connsp_2(E_433, '#skF_4', '#skF_8') | ~r1_tarski(E_433, u1_struct_0('#skF_6')) | ~m1_subset_1(E_433, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_58, c_133, c_351])).
% 10.44/3.86  tff(c_357, plain, (![B_44, C_50]: (~m1_connsp_2('#skF_2'('#skF_4', B_44, C_50), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_44, C_50), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_50, '#skF_4', B_44) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_353])).
% 10.44/3.86  tff(c_372, plain, (![B_44, C_50]: (~m1_connsp_2('#skF_2'('#skF_4', B_44, C_50), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_44, C_50), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_50, '#skF_4', B_44) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_357])).
% 10.44/3.86  tff(c_484, plain, (![B_445, C_446]: (~m1_connsp_2('#skF_2'('#skF_4', B_445, C_446), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_445, C_446), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_446, '#skF_4', B_445) | ~m1_subset_1(C_446, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_445, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_372])).
% 10.44/3.86  tff(c_488, plain, (![B_366]: (~m1_connsp_2('#skF_2'('#skF_4', B_366, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_366) | ~m1_subset_1(B_366, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_252, c_484])).
% 10.44/3.86  tff(c_495, plain, (![B_366]: (~m1_connsp_2('#skF_2'('#skF_4', B_366, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_366) | ~m1_subset_1(B_366, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_68, c_488])).
% 10.44/3.86  tff(c_496, plain, (![B_366]: (~m1_connsp_2('#skF_2'('#skF_4', B_366, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_366) | ~m1_subset_1(B_366, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_495])).
% 10.44/3.86  tff(c_501, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_496])).
% 10.44/3.86  tff(c_504, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_501])).
% 10.44/3.86  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_504])).
% 10.44/3.86  tff(c_513, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_496])).
% 10.44/3.86  tff(c_56, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_289])).
% 10.44/3.86  tff(c_214, plain, (![B_350, A_351]: (v3_pre_topc(u1_struct_0(B_350), A_351) | ~v1_tsep_1(B_350, A_351) | ~m1_subset_1(u1_struct_0(B_350), k1_zfmisc_1(u1_struct_0(A_351))) | ~m1_pre_topc(B_350, A_351) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.44/3.86  tff(c_221, plain, (![B_63, A_61]: (v3_pre_topc(u1_struct_0(B_63), A_61) | ~v1_tsep_1(B_63, A_61) | ~v2_pre_topc(A_61) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_40, c_214])).
% 10.44/3.86  tff(c_121, plain, (![B_320, A_321]: (v2_pre_topc(B_320) | ~m1_pre_topc(B_320, A_321) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.44/3.86  tff(c_124, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_121])).
% 10.44/3.86  tff(c_127, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_124])).
% 10.44/3.86  tff(c_94, plain, (![B_312, A_313]: (l1_pre_topc(B_312) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.44/3.86  tff(c_97, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_94])).
% 10.44/3.86  tff(c_100, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_97])).
% 10.44/3.86  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.44/3.86  tff(c_28, plain, (![A_32, B_44, C_50]: (r1_tarski('#skF_2'(A_32, B_44, C_50), C_50) | ~m1_connsp_2(C_50, A_32, B_44) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_522, plain, (![B_44]: (r1_tarski('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_513, c_28])).
% 10.44/3.86  tff(c_539, plain, (![B_44]: (r1_tarski('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_522])).
% 10.44/3.86  tff(c_540, plain, (![B_44]: (r1_tarski('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_539])).
% 10.44/3.86  tff(c_26, plain, (![B_44, A_32, C_50]: (r2_hidden(B_44, '#skF_2'(A_32, B_44, C_50)) | ~m1_connsp_2(C_50, A_32, B_44) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_518, plain, (![B_44]: (r2_hidden(B_44, '#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_513, c_26])).
% 10.44/3.86  tff(c_531, plain, (![B_44]: (r2_hidden(B_44, '#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_518])).
% 10.44/3.86  tff(c_547, plain, (![B_451]: (r2_hidden(B_451, '#skF_2'('#skF_4', B_451, u1_struct_0('#skF_6'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_451) | ~m1_subset_1(B_451, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_531])).
% 10.44/3.86  tff(c_24, plain, (![C_50, A_32, B_44, D_53]: (m1_connsp_2(C_50, A_32, B_44) | ~r2_hidden(B_44, D_53) | ~r1_tarski(D_53, C_50) | ~v3_pre_topc(D_53, A_32) | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_44, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_626, plain, (![C_476, A_477, B_478]: (m1_connsp_2(C_476, A_477, B_478) | ~r1_tarski('#skF_2'('#skF_4', B_478, u1_struct_0('#skF_6')), C_476) | ~v3_pre_topc('#skF_2'('#skF_4', B_478, u1_struct_0('#skF_6')), A_477) | ~m1_subset_1('#skF_2'('#skF_4', B_478, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0(A_477))) | ~m1_subset_1(C_476, k1_zfmisc_1(u1_struct_0(A_477))) | ~m1_subset_1(B_478, u1_struct_0(A_477)) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_478) | ~m1_subset_1(B_478, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_547, c_24])).
% 10.44/3.86  tff(c_917, plain, (![B_532, A_533]: (m1_connsp_2('#skF_2'('#skF_4', B_532, u1_struct_0('#skF_6')), A_533, B_532) | ~v3_pre_topc('#skF_2'('#skF_4', B_532, u1_struct_0('#skF_6')), A_533) | ~m1_subset_1('#skF_2'('#skF_4', B_532, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0(A_533))) | ~m1_subset_1(B_532, u1_struct_0(A_533)) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_532) | ~m1_subset_1(B_532, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_626])).
% 10.44/3.86  tff(c_1063, plain, (![B_547, A_548]: (m1_connsp_2('#skF_2'('#skF_4', B_547, u1_struct_0('#skF_6')), A_548, B_547) | ~v3_pre_topc('#skF_2'('#skF_4', B_547, u1_struct_0('#skF_6')), A_548) | ~m1_subset_1(B_547, u1_struct_0(A_548)) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548) | v2_struct_0(A_548) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_547) | ~m1_subset_1(B_547, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_2'('#skF_4', B_547, u1_struct_0('#skF_6')), u1_struct_0(A_548)))), inference(resolution, [status(thm)], [c_10, c_917])).
% 10.44/3.86  tff(c_1067, plain, (![B_44]: (m1_connsp_2('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), '#skF_6', B_44) | ~v3_pre_topc('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_44, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_540, c_1063])).
% 10.44/3.86  tff(c_1083, plain, (![B_44]: (m1_connsp_2('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), '#skF_6', B_44) | ~v3_pre_topc('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_44, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_1067])).
% 10.44/3.86  tff(c_1097, plain, (![B_549]: (m1_connsp_2('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), '#skF_6', B_549) | ~v3_pre_topc('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_549, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_549) | ~m1_subset_1(B_549, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1083])).
% 10.44/3.86  tff(c_18, plain, (![C_21, A_18, B_19]: (m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_connsp_2(C_21, A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/3.86  tff(c_1101, plain, (![B_549]: (m1_subset_1('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_549, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_549) | ~m1_subset_1(B_549, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1097, c_18])).
% 10.44/3.86  tff(c_1108, plain, (![B_549]: (m1_subset_1('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_549, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_549, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_549) | ~m1_subset_1(B_549, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_1101])).
% 10.44/3.86  tff(c_1110, plain, (![B_550]: (m1_subset_1('#skF_2'('#skF_4', B_550, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_550, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_550) | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1108])).
% 10.44/3.86  tff(c_128, plain, (![B_322, A_323]: (m1_subset_1(u1_struct_0(B_322), k1_zfmisc_1(u1_struct_0(A_323))) | ~m1_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.44/3.86  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.44/3.86  tff(c_132, plain, (![B_322, A_323]: (r1_tarski(u1_struct_0(B_322), u1_struct_0(A_323)) | ~m1_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323))), inference(resolution, [status(thm)], [c_128, c_8])).
% 10.44/3.86  tff(c_382, plain, (![A_434]: (~m1_connsp_2(A_434, '#skF_4', '#skF_8') | ~r1_tarski(A_434, u1_struct_0('#skF_6')) | ~r1_tarski(A_434, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_353])).
% 10.44/3.86  tff(c_420, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_382])).
% 10.44/3.86  tff(c_421, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_420])).
% 10.44/3.86  tff(c_425, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_132, c_421])).
% 10.44/3.86  tff(c_429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_425])).
% 10.44/3.86  tff(c_431, plain, (r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_420])).
% 10.44/3.86  tff(c_270, plain, (![B_377, A_378, C_379]: (r2_hidden(B_377, '#skF_2'(A_378, B_377, C_379)) | ~m1_connsp_2(C_379, A_378, B_377) | ~m1_subset_1(C_379, k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_subset_1(B_377, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_280, plain, (![B_377, A_378, A_3]: (r2_hidden(B_377, '#skF_2'(A_378, B_377, A_3)) | ~m1_connsp_2(A_3, A_378, B_377) | ~m1_subset_1(B_377, u1_struct_0(A_378)) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378) | ~r1_tarski(A_3, u1_struct_0(A_378)))), inference(resolution, [status(thm)], [c_10, c_270])).
% 10.44/3.86  tff(c_302, plain, (![C_395, A_396, B_397, D_398]: (m1_connsp_2(C_395, A_396, B_397) | ~r2_hidden(B_397, D_398) | ~r1_tarski(D_398, C_395) | ~v3_pre_topc(D_398, A_396) | ~m1_subset_1(D_398, k1_zfmisc_1(u1_struct_0(A_396))) | ~m1_subset_1(C_395, k1_zfmisc_1(u1_struct_0(A_396))) | ~m1_subset_1(B_397, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_839, plain, (![A_517, A_516, B_519, C_520, A_518]: (m1_connsp_2(C_520, A_516, B_519) | ~r1_tarski('#skF_2'(A_518, B_519, A_517), C_520) | ~v3_pre_topc('#skF_2'(A_518, B_519, A_517), A_516) | ~m1_subset_1('#skF_2'(A_518, B_519, A_517), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(C_520, k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(B_519, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516) | ~m1_connsp_2(A_517, A_518, B_519) | ~m1_subset_1(B_519, u1_struct_0(A_518)) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518) | ~r1_tarski(A_517, u1_struct_0(A_518)))), inference(resolution, [status(thm)], [c_280, c_302])).
% 10.44/3.86  tff(c_845, plain, (![A_516, B_44]: (m1_connsp_2(u1_struct_0('#skF_6'), A_516, B_44) | ~v3_pre_topc('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), A_516) | ~m1_subset_1('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(B_44, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_540, c_839])).
% 10.44/3.86  tff(c_864, plain, (![A_516, B_44]: (m1_connsp_2(u1_struct_0('#skF_6'), A_516, B_44) | ~v3_pre_topc('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), A_516) | ~m1_subset_1('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(B_44, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516) | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_68, c_66, c_845])).
% 10.44/3.86  tff(c_865, plain, (![A_516, B_44]: (m1_connsp_2(u1_struct_0('#skF_6'), A_516, B_44) | ~v3_pre_topc('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), A_516) | ~m1_subset_1('#skF_2'('#skF_4', B_44, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_516))) | ~m1_subset_1(B_44, u1_struct_0(A_516)) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516) | v2_struct_0(A_516) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_44) | ~m1_subset_1(B_44, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_864])).
% 10.44/3.86  tff(c_1115, plain, (![B_550]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_550) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_550, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_550) | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1110, c_865])).
% 10.44/3.86  tff(c_1134, plain, (![B_550]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_550) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | ~v3_pre_topc('#skF_2'('#skF_4', B_550, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_550) | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_1115])).
% 10.44/3.86  tff(c_1135, plain, (![B_550]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_550) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_2'('#skF_4', B_550, u1_struct_0('#skF_6')), '#skF_6') | ~m1_subset_1(B_550, u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_550) | ~m1_subset_1(B_550, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1134])).
% 10.44/3.86  tff(c_1154, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_1135])).
% 10.44/3.86  tff(c_1160, plain, (~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_1154])).
% 10.44/3.86  tff(c_1167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1160])).
% 10.44/3.86  tff(c_1169, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_1135])).
% 10.44/3.86  tff(c_20, plain, (![A_22, B_23]: (m1_connsp_2('#skF_1'(A_22, B_23), A_22, B_23) | ~m1_subset_1(B_23, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.44/3.86  tff(c_192, plain, (![C_341, A_342, B_343]: (m1_subset_1(C_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_connsp_2(C_341, A_342, B_343) | ~m1_subset_1(B_343, u1_struct_0(A_342)) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342) | v2_struct_0(A_342))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.44/3.86  tff(c_196, plain, (![A_344, B_345]: (m1_subset_1('#skF_1'(A_344, B_345), k1_zfmisc_1(u1_struct_0(A_344))) | ~m1_subset_1(B_345, u1_struct_0(A_344)) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_20, c_192])).
% 10.44/3.86  tff(c_200, plain, (![A_344, B_345]: (r1_tarski('#skF_1'(A_344, B_345), u1_struct_0(A_344)) | ~m1_subset_1(B_345, u1_struct_0(A_344)) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(resolution, [status(thm)], [c_196, c_8])).
% 10.44/3.86  tff(c_258, plain, (![A_371, B_372, C_373]: (v3_pre_topc('#skF_2'(A_371, B_372, C_373), A_371) | ~m1_connsp_2(C_373, A_371, B_372) | ~m1_subset_1(C_373, k1_zfmisc_1(u1_struct_0(A_371))) | ~m1_subset_1(B_372, u1_struct_0(A_371)) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_268, plain, (![A_371, B_372, A_3]: (v3_pre_topc('#skF_2'(A_371, B_372, A_3), A_371) | ~m1_connsp_2(A_3, A_371, B_372) | ~m1_subset_1(B_372, u1_struct_0(A_371)) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371) | ~r1_tarski(A_3, u1_struct_0(A_371)))), inference(resolution, [status(thm)], [c_10, c_258])).
% 10.44/3.86  tff(c_288, plain, (![A_392, B_393, C_394]: (m1_subset_1('#skF_2'(A_392, B_393, C_394), k1_zfmisc_1(u1_struct_0(A_392))) | ~m1_connsp_2(C_394, A_392, B_393) | ~m1_subset_1(C_394, k1_zfmisc_1(u1_struct_0(A_392))) | ~m1_subset_1(B_393, u1_struct_0(A_392)) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.44/3.86  tff(c_301, plain, (![A_392, B_393, C_394]: (r1_tarski('#skF_2'(A_392, B_393, C_394), u1_struct_0(A_392)) | ~m1_connsp_2(C_394, A_392, B_393) | ~m1_subset_1(C_394, k1_zfmisc_1(u1_struct_0(A_392))) | ~m1_subset_1(B_393, u1_struct_0(A_392)) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_288, c_8])).
% 10.44/3.86  tff(c_2404, plain, (![A_697, A_698, B_699, C_700]: (m1_connsp_2(u1_struct_0(A_697), A_698, B_699) | ~v3_pre_topc('#skF_2'(A_697, B_699, C_700), A_698) | ~m1_subset_1('#skF_2'(A_697, B_699, C_700), k1_zfmisc_1(u1_struct_0(A_698))) | ~m1_subset_1(u1_struct_0(A_697), k1_zfmisc_1(u1_struct_0(A_698))) | ~m1_subset_1(B_699, u1_struct_0(A_698)) | ~l1_pre_topc(A_698) | ~v2_pre_topc(A_698) | v2_struct_0(A_698) | ~r1_tarski(C_700, u1_struct_0(A_697)) | ~m1_connsp_2(C_700, A_697, B_699) | ~m1_subset_1(C_700, k1_zfmisc_1(u1_struct_0(A_697))) | ~m1_subset_1(B_699, u1_struct_0(A_697)) | ~l1_pre_topc(A_697) | ~v2_pre_topc(A_697) | v2_struct_0(A_697))), inference(resolution, [status(thm)], [c_301, c_839])).
% 10.44/3.86  tff(c_2445, plain, (![A_701, B_702, C_703]: (m1_connsp_2(u1_struct_0(A_701), A_701, B_702) | ~v3_pre_topc('#skF_2'(A_701, B_702, C_703), A_701) | ~m1_subset_1(u1_struct_0(A_701), k1_zfmisc_1(u1_struct_0(A_701))) | ~r1_tarski(C_703, u1_struct_0(A_701)) | ~m1_connsp_2(C_703, A_701, B_702) | ~m1_subset_1(C_703, k1_zfmisc_1(u1_struct_0(A_701))) | ~m1_subset_1(B_702, u1_struct_0(A_701)) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(resolution, [status(thm)], [c_32, c_2404])).
% 10.44/3.86  tff(c_2506, plain, (![A_704, B_705, A_706]: (m1_connsp_2(u1_struct_0(A_704), A_704, B_705) | ~m1_subset_1(u1_struct_0(A_704), k1_zfmisc_1(u1_struct_0(A_704))) | ~m1_subset_1(A_706, k1_zfmisc_1(u1_struct_0(A_704))) | ~m1_connsp_2(A_706, A_704, B_705) | ~m1_subset_1(B_705, u1_struct_0(A_704)) | ~l1_pre_topc(A_704) | ~v2_pre_topc(A_704) | v2_struct_0(A_704) | ~r1_tarski(A_706, u1_struct_0(A_704)))), inference(resolution, [status(thm)], [c_268, c_2445])).
% 10.44/3.86  tff(c_2508, plain, (![B_705, A_706]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_705) | ~m1_subset_1(A_706, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_706, '#skF_6', B_705) | ~m1_subset_1(B_705, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_706, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1169, c_2506])).
% 10.44/3.86  tff(c_2519, plain, (![B_705, A_706]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_705) | ~m1_subset_1(A_706, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_706, '#skF_6', B_705) | ~m1_subset_1(B_705, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r1_tarski(A_706, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_2508])).
% 10.44/3.86  tff(c_2591, plain, (![B_709, A_710]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_709) | ~m1_subset_1(A_710, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_710, '#skF_6', B_709) | ~m1_subset_1(B_709, u1_struct_0('#skF_6')) | ~r1_tarski(A_710, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2519])).
% 10.44/3.86  tff(c_2728, plain, (![B_716, A_717]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_716) | ~m1_connsp_2(A_717, '#skF_6', B_716) | ~m1_subset_1(B_716, u1_struct_0('#skF_6')) | ~r1_tarski(A_717, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_10, c_2591])).
% 10.44/3.86  tff(c_2749, plain, (![B_23]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_23) | ~r1_tarski('#skF_1'('#skF_6', B_23), u1_struct_0('#skF_6')) | ~m1_subset_1(B_23, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_2728])).
% 10.44/3.86  tff(c_2773, plain, (![B_23]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_23) | ~r1_tarski('#skF_1'('#skF_6', B_23), u1_struct_0('#skF_6')) | ~m1_subset_1(B_23, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_2749])).
% 10.44/3.86  tff(c_2775, plain, (![B_718]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_718) | ~r1_tarski('#skF_1'('#skF_6', B_718), u1_struct_0('#skF_6')) | ~m1_subset_1(B_718, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2773])).
% 10.44/3.86  tff(c_2779, plain, (![B_345]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_345) | ~m1_subset_1(B_345, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_200, c_2775])).
% 10.44/3.86  tff(c_2782, plain, (![B_345]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_345) | ~m1_subset_1(B_345, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_2779])).
% 10.44/3.86  tff(c_2784, plain, (![B_719]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_6', B_719) | ~m1_subset_1(B_719, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2782])).
% 10.44/3.86  tff(c_22, plain, (![C_31, B_29, A_25]: (r2_hidden(C_31, B_29) | ~m1_connsp_2(B_29, A_25, C_31) | ~m1_subset_1(C_31, u1_struct_0(A_25)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.44/3.86  tff(c_2786, plain, (![B_719]: (r2_hidden(B_719, u1_struct_0('#skF_6')) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_subset_1(B_719, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_2784, c_22])).
% 10.44/3.86  tff(c_2791, plain, (![B_719]: (r2_hidden(B_719, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~m1_subset_1(B_719, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_100, c_1169, c_2786])).
% 10.44/3.86  tff(c_2797, plain, (![B_720]: (r2_hidden(B_720, u1_struct_0('#skF_6')) | ~m1_subset_1(B_720, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_58, c_2791])).
% 10.44/3.86  tff(c_3696, plain, (![C_821, A_822, B_823]: (m1_connsp_2(C_821, A_822, B_823) | ~r1_tarski(u1_struct_0('#skF_6'), C_821) | ~v3_pre_topc(u1_struct_0('#skF_6'), A_822) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_822))) | ~m1_subset_1(C_821, k1_zfmisc_1(u1_struct_0(A_822))) | ~m1_subset_1(B_823, u1_struct_0(A_822)) | ~l1_pre_topc(A_822) | ~v2_pre_topc(A_822) | v2_struct_0(A_822) | ~m1_subset_1(B_823, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_2797, c_24])).
% 10.44/3.86  tff(c_3706, plain, (![C_821, B_823]: (m1_connsp_2(C_821, '#skF_4', B_823) | ~r1_tarski(u1_struct_0('#skF_6'), C_821) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~m1_subset_1(C_821, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_823, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(B_823, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_513, c_3696])).
% 10.44/3.86  tff(c_3727, plain, (![C_821, B_823]: (m1_connsp_2(C_821, '#skF_4', B_823) | ~r1_tarski(u1_struct_0('#skF_6'), C_821) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~m1_subset_1(C_821, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_823, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(B_823, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_3706])).
% 10.44/3.86  tff(c_3728, plain, (![C_821, B_823]: (m1_connsp_2(C_821, '#skF_4', B_823) | ~r1_tarski(u1_struct_0('#skF_6'), C_821) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~m1_subset_1(C_821, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_823, u1_struct_0('#skF_4')) | ~m1_subset_1(B_823, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_70, c_3727])).
% 10.44/3.86  tff(c_3754, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3728])).
% 10.44/3.86  tff(c_3757, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_221, c_3754])).
% 10.44/3.86  tff(c_3761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_68, c_56, c_3757])).
% 10.44/3.86  tff(c_3770, plain, (![C_829, B_830]: (m1_connsp_2(C_829, '#skF_4', B_830) | ~r1_tarski(u1_struct_0('#skF_6'), C_829) | ~m1_subset_1(C_829, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_830, u1_struct_0('#skF_4')) | ~m1_subset_1(B_830, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_3728])).
% 10.44/3.86  tff(c_3799, plain, (![B_830]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_830) | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_6')) | ~m1_subset_1(B_830, u1_struct_0('#skF_4')) | ~m1_subset_1(B_830, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_513, c_3770])).
% 10.44/3.86  tff(c_3860, plain, (![B_831]: (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_831) | ~m1_subset_1(B_831, u1_struct_0('#skF_4')) | ~m1_subset_1(B_831, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3799])).
% 10.44/3.86  tff(c_430, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_420])).
% 10.44/3.86  tff(c_3867, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_3860, c_430])).
% 10.44/3.86  tff(c_3878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_86, c_3867])).
% 10.44/3.86  tff(c_3880, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 10.44/3.86  tff(c_4070, plain, (![B_922, D_920, C_921, F_919, A_923]: (r1_tmap_1(D_920, A_923, k2_tmap_1(B_922, A_923, C_921, D_920), F_919) | ~r1_tmap_1(B_922, A_923, C_921, F_919) | ~m1_subset_1(F_919, u1_struct_0(D_920)) | ~m1_subset_1(F_919, u1_struct_0(B_922)) | ~m1_pre_topc(D_920, B_922) | v2_struct_0(D_920) | ~m1_subset_1(C_921, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_922), u1_struct_0(A_923)))) | ~v1_funct_2(C_921, u1_struct_0(B_922), u1_struct_0(A_923)) | ~v1_funct_1(C_921) | ~l1_pre_topc(B_922) | ~v2_pre_topc(B_922) | v2_struct_0(B_922) | ~l1_pre_topc(A_923) | ~v2_pre_topc(A_923) | v2_struct_0(A_923))), inference(cnfTransformation, [status(thm)], [f_199])).
% 10.44/3.86  tff(c_4072, plain, (![D_920, F_919]: (r1_tmap_1(D_920, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_920), F_919) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_919) | ~m1_subset_1(F_919, u1_struct_0(D_920)) | ~m1_subset_1(F_919, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_920, '#skF_4') | v2_struct_0(D_920) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_4070])).
% 10.44/3.86  tff(c_4078, plain, (![D_920, F_919]: (r1_tmap_1(D_920, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_920), F_919) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_919) | ~m1_subset_1(F_919, u1_struct_0(D_920)) | ~m1_subset_1(F_919, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_920, '#skF_4') | v2_struct_0(D_920) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_62, c_4072])).
% 10.44/3.86  tff(c_4081, plain, (![D_924, F_925]: (r1_tmap_1(D_924, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_924), F_925) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_925) | ~m1_subset_1(F_925, u1_struct_0(D_924)) | ~m1_subset_1(F_925, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_924, '#skF_4') | v2_struct_0(D_924))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_4078])).
% 10.44/3.86  tff(c_3879, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 10.44/3.86  tff(c_4084, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4081, c_3879])).
% 10.44/3.86  tff(c_4087, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_86, c_50, c_3880, c_4084])).
% 10.44/3.86  tff(c_4089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4087])).
% 10.44/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.44/3.86  
% 10.44/3.86  Inference rules
% 10.44/3.86  ----------------------
% 10.44/3.86  #Ref     : 0
% 10.44/3.86  #Sup     : 731
% 10.44/3.86  #Fact    : 0
% 10.44/3.86  #Define  : 0
% 10.44/3.86  #Split   : 16
% 10.44/3.86  #Chain   : 0
% 10.44/3.86  #Close   : 0
% 10.44/3.86  
% 10.44/3.86  Ordering : KBO
% 10.44/3.86  
% 10.44/3.86  Simplification rules
% 10.44/3.86  ----------------------
% 10.44/3.86  #Subsume      : 309
% 10.44/3.86  #Demod        : 976
% 10.44/3.86  #Tautology    : 80
% 10.44/3.86  #SimpNegUnit  : 311
% 10.44/3.86  #BackRed      : 0
% 10.44/3.86  
% 10.44/3.86  #Partial instantiations: 0
% 10.44/3.86  #Strategies tried      : 1
% 10.44/3.86  
% 10.44/3.86  Timing (in seconds)
% 10.44/3.86  ----------------------
% 10.44/3.87  Preprocessing        : 0.63
% 10.44/3.87  Parsing              : 0.31
% 10.44/3.87  CNF conversion       : 0.08
% 10.44/3.87  Main loop            : 2.26
% 10.44/3.87  Inferencing          : 0.83
% 10.44/3.87  Reduction            : 0.61
% 10.44/3.87  Demodulation         : 0.42
% 10.44/3.87  BG Simplification    : 0.07
% 10.44/3.87  Subsumption          : 0.62
% 10.44/3.87  Abstraction          : 0.09
% 10.44/3.87  MUC search           : 0.00
% 10.44/3.87  Cooper               : 0.00
% 10.44/3.87  Total                : 2.98
% 10.44/3.87  Index Insertion      : 0.00
% 10.44/3.87  Index Deletion       : 0.00
% 10.44/3.87  Index Matching       : 0.00
% 10.44/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
