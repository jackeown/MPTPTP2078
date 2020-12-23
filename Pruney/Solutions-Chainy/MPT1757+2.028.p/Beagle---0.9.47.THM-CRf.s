%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:08 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 469 expanded)
%              Number of leaves         :   40 ( 198 expanded)
%              Depth                    :   24
%              Number of atoms          :  353 (3436 expanded)
%              Number of equality atoms :    5 ( 168 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_261,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_124,axiom,(
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

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_218,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_171,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_46,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_40,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_58,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_85,plain,(
    ! [B_302,A_303] :
      ( l1_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_48,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_32,plain,(
    ! [B_53,A_51] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_145,plain,(
    ! [B_329,A_330] :
      ( v3_pre_topc(u1_struct_0(B_329),A_330)
      | ~ v1_tsep_1(B_329,A_330)
      | ~ m1_subset_1(u1_struct_0(B_329),k1_zfmisc_1(u1_struct_0(A_330)))
      | ~ m1_pre_topc(B_329,A_330)
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_149,plain,(
    ! [B_53,A_51] :
      ( v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v1_tsep_1(B_53,A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_32,c_145])).

tff(c_150,plain,(
    ! [A_331,B_332,C_333] :
      ( r1_tarski('#skF_1'(A_331,B_332,C_333),B_332)
      | ~ r2_hidden(C_333,B_332)
      | ~ m1_subset_1(C_333,u1_struct_0(A_331))
      | ~ v3_pre_topc(B_332,A_331)
      | ~ m1_subset_1(B_332,k1_zfmisc_1(u1_struct_0(A_331)))
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_153,plain,(
    ! [A_51,B_53,C_333] :
      ( r1_tarski('#skF_1'(A_51,u1_struct_0(B_53),C_333),u1_struct_0(B_53))
      | ~ r2_hidden(C_333,u1_struct_0(B_53))
      | ~ m1_subset_1(C_333,u1_struct_0(A_51))
      | ~ v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_24,plain,(
    ! [A_19,B_33,C_40] :
      ( m1_subset_1('#skF_1'(A_19,B_33,C_40),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0(A_19))
      | ~ v3_pre_topc(B_33,A_19)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70])).

tff(c_93,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_96,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_77])).

tff(c_250,plain,(
    ! [A_397,B_393,G_396,C_398,E_394,D_395] :
      ( r1_tmap_1(B_393,A_397,C_398,G_396)
      | ~ r1_tmap_1(D_395,A_397,k2_tmap_1(B_393,A_397,C_398,D_395),G_396)
      | ~ m1_connsp_2(E_394,B_393,G_396)
      | ~ r1_tarski(E_394,u1_struct_0(D_395))
      | ~ m1_subset_1(G_396,u1_struct_0(D_395))
      | ~ m1_subset_1(G_396,u1_struct_0(B_393))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0(B_393)))
      | ~ m1_pre_topc(D_395,B_393)
      | v2_struct_0(D_395)
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393),u1_struct_0(A_397))))
      | ~ v1_funct_2(C_398,u1_struct_0(B_393),u1_struct_0(A_397))
      | ~ v1_funct_1(C_398)
      | ~ l1_pre_topc(B_393)
      | ~ v2_pre_topc(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_254,plain,(
    ! [E_394] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_394,'#skF_4','#skF_8')
      | ~ r1_tarski(E_394,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_96,c_250])).

tff(c_261,plain,(
    ! [E_394] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_394,'#skF_4','#skF_8')
      | ~ r1_tarski(E_394,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_52,c_46,c_78,c_42,c_254])).

tff(c_263,plain,(
    ! [E_399] :
      ( ~ m1_connsp_2(E_399,'#skF_4','#skF_8')
      | ~ r1_tarski(E_399,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_399,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_50,c_93,c_261])).

tff(c_275,plain,(
    ! [B_33,C_40] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_33,C_40),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_33,C_40),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_33,'#skF_4')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_263])).

tff(c_290,plain,(
    ! [B_33,C_40] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_33,C_40),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_33,C_40),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_33,'#skF_4')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_275])).

tff(c_296,plain,(
    ! [B_401,C_402] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_401,C_402),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_401,C_402),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_402,B_401)
      | ~ m1_subset_1(C_402,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_401,'#skF_4')
      | ~ m1_subset_1(B_401,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_290])).

tff(c_300,plain,(
    ! [C_333] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_333),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_333,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_153,c_296])).

tff(c_303,plain,(
    ! [C_333] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_333),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_333,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_300])).

tff(c_304,plain,(
    ! [C_333] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_333),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_333,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_303])).

tff(c_305,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_308,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_48,c_308])).

tff(c_314,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_165,plain,(
    ! [A_344,B_345,C_346] :
      ( m1_connsp_2('#skF_1'(A_344,B_345,C_346),A_344,C_346)
      | ~ r2_hidden(C_346,B_345)
      | ~ m1_subset_1(C_346,u1_struct_0(A_344))
      | ~ v3_pre_topc(B_345,A_344)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344)
      | ~ v2_pre_topc(A_344)
      | v2_struct_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_168,plain,(
    ! [A_51,B_53,C_346] :
      ( m1_connsp_2('#skF_1'(A_51,u1_struct_0(B_53),C_346),A_51,C_346)
      | ~ r2_hidden(C_346,u1_struct_0(B_53))
      | ~ m1_subset_1(C_346,u1_struct_0(A_51))
      | ~ v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_32,c_165])).

tff(c_313,plain,(
    ! [C_333] :
      ( ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_333),'#skF_4','#skF_8')
      | ~ r2_hidden(C_333,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_321,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_324,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_324])).

tff(c_355,plain,(
    ! [C_407] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_407),'#skF_4','#skF_8')
      | ~ r2_hidden(C_407,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_407,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_359,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_355])).

tff(c_362,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_314,c_78,c_359])).

tff(c_363,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_362])).

tff(c_366,plain,
    ( v1_xboole_0(u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2,c_363])).

tff(c_369,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_366])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_372,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_369,c_8])).

tff(c_375,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_372])).

tff(c_378,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_375])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_378])).

tff(c_384,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_471,plain,(
    ! [C_454,B_453,F_457,D_456,A_455] :
      ( r1_tmap_1(D_456,A_455,k2_tmap_1(B_453,A_455,C_454,D_456),F_457)
      | ~ r1_tmap_1(B_453,A_455,C_454,F_457)
      | ~ m1_subset_1(F_457,u1_struct_0(D_456))
      | ~ m1_subset_1(F_457,u1_struct_0(B_453))
      | ~ m1_pre_topc(D_456,B_453)
      | v2_struct_0(D_456)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453),u1_struct_0(A_455))))
      | ~ v1_funct_2(C_454,u1_struct_0(B_453),u1_struct_0(A_455))
      | ~ v1_funct_1(C_454)
      | ~ l1_pre_topc(B_453)
      | ~ v2_pre_topc(B_453)
      | v2_struct_0(B_453)
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_473,plain,(
    ! [D_456,F_457] :
      ( r1_tmap_1(D_456,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_456),F_457)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_457)
      | ~ m1_subset_1(F_457,u1_struct_0(D_456))
      | ~ m1_subset_1(F_457,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_456,'#skF_4')
      | v2_struct_0(D_456)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_476,plain,(
    ! [D_456,F_457] :
      ( r1_tmap_1(D_456,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_456),F_457)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_457)
      | ~ m1_subset_1(F_457,u1_struct_0(D_456))
      | ~ m1_subset_1(F_457,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_456,'#skF_4')
      | v2_struct_0(D_456)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_473])).

tff(c_478,plain,(
    ! [D_458,F_459] :
      ( r1_tmap_1(D_458,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_458),F_459)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_459)
      | ~ m1_subset_1(F_459,u1_struct_0(D_458))
      | ~ m1_subset_1(F_459,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_458,'#skF_4')
      | v2_struct_0(D_458) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_476])).

tff(c_383,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_481,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_478,c_383])).

tff(c_484,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_78,c_42,c_384,c_481])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  
% 3.34/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.34/1.56  
% 3.34/1.56  %Foreground sorts:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Background operators:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Foreground operators:
% 3.34/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.34/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.34/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.34/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.34/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.34/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.56  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.34/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.34/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.56  
% 3.54/1.58  tff(f_261, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.54/1.58  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.54/1.58  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.54/1.58  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.54/1.58  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.54/1.58  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.54/1.58  tff(f_106, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.54/1.58  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.54/1.58  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.54/1.58  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.54/1.58  tff(c_50, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_46, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_78, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 3.54/1.58  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_58, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_85, plain, (![B_302, A_303]: (l1_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.54/1.58  tff(c_88, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_85])).
% 3.54/1.58  tff(c_91, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88])).
% 3.54/1.58  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.58  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.58  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_48, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_32, plain, (![B_53, A_51]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.54/1.58  tff(c_145, plain, (![B_329, A_330]: (v3_pre_topc(u1_struct_0(B_329), A_330) | ~v1_tsep_1(B_329, A_330) | ~m1_subset_1(u1_struct_0(B_329), k1_zfmisc_1(u1_struct_0(A_330))) | ~m1_pre_topc(B_329, A_330) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.54/1.58  tff(c_149, plain, (![B_53, A_51]: (v3_pre_topc(u1_struct_0(B_53), A_51) | ~v1_tsep_1(B_53, A_51) | ~v2_pre_topc(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_32, c_145])).
% 3.54/1.58  tff(c_150, plain, (![A_331, B_332, C_333]: (r1_tarski('#skF_1'(A_331, B_332, C_333), B_332) | ~r2_hidden(C_333, B_332) | ~m1_subset_1(C_333, u1_struct_0(A_331)) | ~v3_pre_topc(B_332, A_331) | ~m1_subset_1(B_332, k1_zfmisc_1(u1_struct_0(A_331))) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.54/1.58  tff(c_153, plain, (![A_51, B_53, C_333]: (r1_tarski('#skF_1'(A_51, u1_struct_0(B_53), C_333), u1_struct_0(B_53)) | ~r2_hidden(C_333, u1_struct_0(B_53)) | ~m1_subset_1(C_333, u1_struct_0(A_51)) | ~v3_pre_topc(u1_struct_0(B_53), A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_32, c_150])).
% 3.54/1.58  tff(c_24, plain, (![A_19, B_33, C_40]: (m1_subset_1('#skF_1'(A_19, B_33, C_40), k1_zfmisc_1(u1_struct_0(A_19))) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0(A_19)) | ~v3_pre_topc(B_33, A_19) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.54/1.58  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_70, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_79, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70])).
% 3.54/1.58  tff(c_93, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_79])).
% 3.54/1.58  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_261])).
% 3.54/1.58  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 3.54/1.58  tff(c_96, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_93, c_77])).
% 3.54/1.58  tff(c_250, plain, (![A_397, B_393, G_396, C_398, E_394, D_395]: (r1_tmap_1(B_393, A_397, C_398, G_396) | ~r1_tmap_1(D_395, A_397, k2_tmap_1(B_393, A_397, C_398, D_395), G_396) | ~m1_connsp_2(E_394, B_393, G_396) | ~r1_tarski(E_394, u1_struct_0(D_395)) | ~m1_subset_1(G_396, u1_struct_0(D_395)) | ~m1_subset_1(G_396, u1_struct_0(B_393)) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0(B_393))) | ~m1_pre_topc(D_395, B_393) | v2_struct_0(D_395) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393), u1_struct_0(A_397)))) | ~v1_funct_2(C_398, u1_struct_0(B_393), u1_struct_0(A_397)) | ~v1_funct_1(C_398) | ~l1_pre_topc(B_393) | ~v2_pre_topc(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.54/1.58  tff(c_254, plain, (![E_394]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_394, '#skF_4', '#skF_8') | ~r1_tarski(E_394, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_96, c_250])).
% 3.54/1.58  tff(c_261, plain, (![E_394]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_394, '#skF_4', '#skF_8') | ~r1_tarski(E_394, u1_struct_0('#skF_6')) | ~m1_subset_1(E_394, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_52, c_46, c_78, c_42, c_254])).
% 3.54/1.58  tff(c_263, plain, (![E_399]: (~m1_connsp_2(E_399, '#skF_4', '#skF_8') | ~r1_tarski(E_399, u1_struct_0('#skF_6')) | ~m1_subset_1(E_399, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_50, c_93, c_261])).
% 3.54/1.58  tff(c_275, plain, (![B_33, C_40]: (~m1_connsp_2('#skF_1'('#skF_4', B_33, C_40), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_33, C_40), u1_struct_0('#skF_6')) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_33, '#skF_4') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_263])).
% 3.54/1.58  tff(c_290, plain, (![B_33, C_40]: (~m1_connsp_2('#skF_1'('#skF_4', B_33, C_40), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_33, C_40), u1_struct_0('#skF_6')) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_33, '#skF_4') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_275])).
% 3.54/1.58  tff(c_296, plain, (![B_401, C_402]: (~m1_connsp_2('#skF_1'('#skF_4', B_401, C_402), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_401, C_402), u1_struct_0('#skF_6')) | ~r2_hidden(C_402, B_401) | ~m1_subset_1(C_402, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_401, '#skF_4') | ~m1_subset_1(B_401, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_290])).
% 3.54/1.58  tff(c_300, plain, (![C_333]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_333), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_333, u1_struct_0('#skF_6')) | ~m1_subset_1(C_333, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_153, c_296])).
% 3.54/1.58  tff(c_303, plain, (![C_333]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_333), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_333, u1_struct_0('#skF_6')) | ~m1_subset_1(C_333, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_300])).
% 3.54/1.58  tff(c_304, plain, (![C_333]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_333), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_333, u1_struct_0('#skF_6')) | ~m1_subset_1(C_333, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_303])).
% 3.54/1.58  tff(c_305, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_304])).
% 3.54/1.58  tff(c_308, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_149, c_305])).
% 3.54/1.58  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_48, c_308])).
% 3.54/1.58  tff(c_314, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_304])).
% 3.54/1.58  tff(c_165, plain, (![A_344, B_345, C_346]: (m1_connsp_2('#skF_1'(A_344, B_345, C_346), A_344, C_346) | ~r2_hidden(C_346, B_345) | ~m1_subset_1(C_346, u1_struct_0(A_344)) | ~v3_pre_topc(B_345, A_344) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344) | ~v2_pre_topc(A_344) | v2_struct_0(A_344))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.54/1.58  tff(c_168, plain, (![A_51, B_53, C_346]: (m1_connsp_2('#skF_1'(A_51, u1_struct_0(B_53), C_346), A_51, C_346) | ~r2_hidden(C_346, u1_struct_0(B_53)) | ~m1_subset_1(C_346, u1_struct_0(A_51)) | ~v3_pre_topc(u1_struct_0(B_53), A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_32, c_165])).
% 3.54/1.58  tff(c_313, plain, (![C_333]: (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_333), '#skF_4', '#skF_8') | ~r2_hidden(C_333, u1_struct_0('#skF_6')) | ~m1_subset_1(C_333, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_304])).
% 3.54/1.58  tff(c_321, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_313])).
% 3.54/1.58  tff(c_324, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_321])).
% 3.54/1.58  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_324])).
% 3.54/1.58  tff(c_355, plain, (![C_407]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_407), '#skF_4', '#skF_8') | ~r2_hidden(C_407, u1_struct_0('#skF_6')) | ~m1_subset_1(C_407, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_313])).
% 3.54/1.58  tff(c_359, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_168, c_355])).
% 3.54/1.58  tff(c_362, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_314, c_78, c_359])).
% 3.54/1.58  tff(c_363, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_362])).
% 3.54/1.58  tff(c_366, plain, (v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_2, c_363])).
% 3.54/1.58  tff(c_369, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_366])).
% 3.54/1.58  tff(c_8, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.58  tff(c_372, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_369, c_8])).
% 3.54/1.58  tff(c_375, plain, (~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_372])).
% 3.54/1.58  tff(c_378, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_4, c_375])).
% 3.54/1.58  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_378])).
% 3.54/1.58  tff(c_384, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_79])).
% 3.54/1.58  tff(c_471, plain, (![C_454, B_453, F_457, D_456, A_455]: (r1_tmap_1(D_456, A_455, k2_tmap_1(B_453, A_455, C_454, D_456), F_457) | ~r1_tmap_1(B_453, A_455, C_454, F_457) | ~m1_subset_1(F_457, u1_struct_0(D_456)) | ~m1_subset_1(F_457, u1_struct_0(B_453)) | ~m1_pre_topc(D_456, B_453) | v2_struct_0(D_456) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453), u1_struct_0(A_455)))) | ~v1_funct_2(C_454, u1_struct_0(B_453), u1_struct_0(A_455)) | ~v1_funct_1(C_454) | ~l1_pre_topc(B_453) | ~v2_pre_topc(B_453) | v2_struct_0(B_453) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.54/1.58  tff(c_473, plain, (![D_456, F_457]: (r1_tmap_1(D_456, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_456), F_457) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_457) | ~m1_subset_1(F_457, u1_struct_0(D_456)) | ~m1_subset_1(F_457, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_456, '#skF_4') | v2_struct_0(D_456) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_471])).
% 3.54/1.58  tff(c_476, plain, (![D_456, F_457]: (r1_tmap_1(D_456, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_456), F_457) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_457) | ~m1_subset_1(F_457, u1_struct_0(D_456)) | ~m1_subset_1(F_457, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_456, '#skF_4') | v2_struct_0(D_456) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_473])).
% 3.54/1.58  tff(c_478, plain, (![D_458, F_459]: (r1_tmap_1(D_458, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_458), F_459) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_459) | ~m1_subset_1(F_459, u1_struct_0(D_458)) | ~m1_subset_1(F_459, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_458, '#skF_4') | v2_struct_0(D_458))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_476])).
% 3.54/1.58  tff(c_383, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_79])).
% 3.54/1.58  tff(c_481, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_478, c_383])).
% 3.54/1.58  tff(c_484, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_78, c_42, c_384, c_481])).
% 3.54/1.58  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_484])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 72
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 4
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 6
% 3.54/1.58  #Demod        : 90
% 3.54/1.58  #Tautology    : 15
% 3.54/1.58  #SimpNegUnit  : 27
% 3.54/1.58  #BackRed      : 0
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.58  Preprocessing        : 0.42
% 3.54/1.58  Parsing              : 0.22
% 3.54/1.58  CNF conversion       : 0.05
% 3.54/1.58  Main loop            : 0.36
% 3.54/1.58  Inferencing          : 0.14
% 3.54/1.58  Reduction            : 0.10
% 3.54/1.59  Demodulation         : 0.07
% 3.54/1.59  BG Simplification    : 0.02
% 3.54/1.59  Subsumption          : 0.07
% 3.54/1.59  Abstraction          : 0.01
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.82
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
