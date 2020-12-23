%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 649 expanded)
%              Number of leaves         :   36 ( 267 expanded)
%              Depth                    :   24
%              Number of atoms          :  412 (5586 expanded)
%              Number of equality atoms :    4 ( 242 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_236,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_186,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( m1_connsp_2(C,A,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( m1_connsp_2(D,A,B)
                          & v3_pre_topc(D,A)
                          & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_139,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_46,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_32,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_77,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_34,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_24,plain,(
    ! [B_43,A_41] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_pre_topc(B_43,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_36,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_311,plain,(
    ! [C_428,A_429,B_430,D_431] :
      ( m1_connsp_2(C_428,A_429,B_430)
      | ~ r2_hidden(B_430,D_431)
      | ~ r1_tarski(D_431,C_428)
      | ~ v3_pre_topc(D_431,A_429)
      | ~ m1_subset_1(D_431,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ m1_subset_1(C_428,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ m1_subset_1(B_430,u1_struct_0(A_429))
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_324,plain,(
    ! [C_432,A_433] :
      ( m1_connsp_2(C_432,A_433,'#skF_8')
      | ~ r1_tarski('#skF_7',C_432)
      | ~ v3_pre_topc('#skF_7',A_433)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_433))
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(resolution,[status(thm)],[c_36,c_311])).

tff(c_326,plain,(
    ! [C_432] :
      ( m1_connsp_2(C_432,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_432)
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_324])).

tff(c_329,plain,(
    ! [C_432] :
      ( m1_connsp_2(C_432,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_38,c_326])).

tff(c_338,plain,(
    ! [C_439] :
      ( m1_connsp_2(C_439,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_329])).

tff(c_360,plain,(
    ! [B_43] :
      ( m1_connsp_2(u1_struct_0(B_43),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_43))
      | ~ m1_pre_topc(B_43,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_338])).

tff(c_420,plain,(
    ! [B_442] :
      ( m1_connsp_2(u1_struct_0(B_442),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_442))
      | ~ m1_pre_topc(B_442,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_360])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( m1_subset_1(C_4,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_connsp_2(C_4,A_1,B_2)
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_422,plain,(
    ! [B_442] :
      ( m1_subset_1(u1_struct_0(B_442),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_442))
      | ~ m1_pre_topc(B_442,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_420,c_2])).

tff(c_425,plain,(
    ! [B_442] :
      ( m1_subset_1(u1_struct_0(B_442),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski('#skF_7',u1_struct_0(B_442))
      | ~ m1_pre_topc(B_442,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_422])).

tff(c_426,plain,(
    ! [B_442] :
      ( m1_subset_1(u1_struct_0(B_442),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_7',u1_struct_0(B_442))
      | ~ m1_pre_topc(B_442,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_425])).

tff(c_87,plain,(
    ! [A_362,B_363,C_364] :
      ( r1_tarski('#skF_2'(A_362,B_363,C_364),C_364)
      | ~ m1_connsp_2(C_364,A_362,B_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_subset_1(B_363,u1_struct_0(A_362))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    ! [A_41,B_363,B_43] :
      ( r1_tarski('#skF_2'(A_41,B_363,u1_struct_0(B_43)),u1_struct_0(B_43))
      | ~ m1_connsp_2(u1_struct_0(B_43),A_41,B_363)
      | ~ m1_subset_1(B_363,u1_struct_0(A_41))
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41)
      | ~ m1_pre_topc(B_43,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_24,c_87])).

tff(c_22,plain,(
    ! [A_19,B_31,C_37] :
      ( m1_subset_1('#skF_2'(A_19,B_31,C_37),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_connsp_2(C_37,A_19,B_31)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_31,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_83,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_75,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_84,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_75])).

tff(c_529,plain,(
    ! [B_449,D_447,E_452,C_448,G_450,A_451] :
      ( r1_tmap_1(B_449,A_451,C_448,G_450)
      | ~ r1_tmap_1(D_447,A_451,k2_tmap_1(B_449,A_451,C_448,D_447),G_450)
      | ~ m1_connsp_2(E_452,B_449,G_450)
      | ~ r1_tarski(E_452,u1_struct_0(D_447))
      | ~ m1_subset_1(G_450,u1_struct_0(D_447))
      | ~ m1_subset_1(G_450,u1_struct_0(B_449))
      | ~ m1_subset_1(E_452,k1_zfmisc_1(u1_struct_0(B_449)))
      | ~ m1_pre_topc(D_447,B_449)
      | v2_struct_0(D_447)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_449),u1_struct_0(A_451))))
      | ~ v1_funct_2(C_448,u1_struct_0(B_449),u1_struct_0(A_451))
      | ~ v1_funct_1(C_448)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | v2_struct_0(B_449)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_531,plain,(
    ! [E_452] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_452,'#skF_4','#skF_8')
      | ~ r1_tarski(E_452,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_452,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_84,c_529])).

tff(c_534,plain,(
    ! [E_452] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_452,'#skF_4','#skF_8')
      | ~ r1_tarski(E_452,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_452,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_46,c_42,c_77,c_531])).

tff(c_536,plain,(
    ! [E_453] :
      ( ~ m1_connsp_2(E_453,'#skF_4','#skF_8')
      | ~ r1_tarski(E_453,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_453,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_48,c_83,c_534])).

tff(c_557,plain,(
    ! [B_31,C_37] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_31,C_37),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_31,C_37),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_37,'#skF_4',B_31)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_536])).

tff(c_581,plain,(
    ! [B_31,C_37] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_31,C_37),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_31,C_37),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_37,'#skF_4',B_31)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_557])).

tff(c_708,plain,(
    ! [B_474,C_475] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_474,C_475),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_4',B_474,C_475),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(C_475,'#skF_4',B_474)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_474,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_581])).

tff(c_716,plain,(
    ! [B_363] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_363,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_363)
      | ~ m1_subset_1(B_363,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_708])).

tff(c_722,plain,(
    ! [B_363] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_363,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_363)
      | ~ m1_subset_1(B_363,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_58,c_716])).

tff(c_723,plain,(
    ! [B_363] :
      ( ~ m1_connsp_2('#skF_2'('#skF_4',B_363,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_363)
      | ~ m1_subset_1(B_363,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_722])).

tff(c_724,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_727,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_426,c_724])).

tff(c_734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_727])).

tff(c_736,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_330,plain,(
    ! [C_432] :
      ( m1_connsp_2(C_432,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_329])).

tff(c_746,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_736,c_330])).

tff(c_764,plain,(
    m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_746])).

tff(c_8,plain,(
    ! [A_5,B_13,C_17] :
      ( m1_connsp_2('#skF_1'(A_5,B_13,C_17),A_5,B_13)
      | ~ m1_connsp_2(C_17,A_5,B_13)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_13,u1_struct_0(A_5))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_748,plain,(
    ! [B_13] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),'#skF_4',B_13)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_736,c_8])).

tff(c_767,plain,(
    ! [B_13] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),'#skF_4',B_13)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_748])).

tff(c_768,plain,(
    ! [B_13] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),'#skF_4',B_13)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_767])).

tff(c_4,plain,(
    ! [A_5,B_13,C_17] :
      ( r1_tarski('#skF_1'(A_5,B_13,C_17),C_17)
      | ~ m1_connsp_2(C_17,A_5,B_13)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_13,u1_struct_0(A_5))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_752,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_736,c_4])).

tff(c_775,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_752])).

tff(c_776,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_1'('#skF_4',B_13,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_13)
      | ~ m1_subset_1(B_13,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_775])).

tff(c_813,plain,(
    ! [B_486] :
      ( m1_connsp_2('#skF_1'('#skF_4',B_486,u1_struct_0('#skF_6')),'#skF_4',B_486)
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_486)
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_767])).

tff(c_815,plain,(
    ! [B_486] :
      ( m1_subset_1('#skF_1'('#skF_4',B_486,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_486)
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_813,c_2])).

tff(c_818,plain,(
    ! [B_486] :
      ( m1_subset_1('#skF_1'('#skF_4',B_486,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_486)
      | ~ m1_subset_1(B_486,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_815])).

tff(c_820,plain,(
    ! [B_487] :
      ( m1_subset_1('#skF_1'('#skF_4',B_487,u1_struct_0('#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_487)
      | ~ m1_subset_1(B_487,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_818])).

tff(c_535,plain,(
    ! [E_452] :
      ( ~ m1_connsp_2(E_452,'#skF_4','#skF_8')
      | ~ r1_tarski(E_452,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_452,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_48,c_83,c_534])).

tff(c_944,plain,(
    ! [B_496] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_496,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_496,u1_struct_0('#skF_6')),u1_struct_0('#skF_6'))
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_496)
      | ~ m1_subset_1(B_496,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_820,c_535])).

tff(c_964,plain,(
    ! [B_497] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_497,u1_struct_0('#skF_6')),'#skF_4','#skF_8')
      | ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_776,c_944])).

tff(c_971,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_768,c_964])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_764,c_971])).

tff(c_986,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1329,plain,(
    ! [B_576,A_579,D_580,F_577,C_578] :
      ( r1_tmap_1(D_580,A_579,k2_tmap_1(B_576,A_579,C_578,D_580),F_577)
      | ~ r1_tmap_1(B_576,A_579,C_578,F_577)
      | ~ m1_subset_1(F_577,u1_struct_0(D_580))
      | ~ m1_subset_1(F_577,u1_struct_0(B_576))
      | ~ m1_pre_topc(D_580,B_576)
      | v2_struct_0(D_580)
      | ~ m1_subset_1(C_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_576),u1_struct_0(A_579))))
      | ~ v1_funct_2(C_578,u1_struct_0(B_576),u1_struct_0(A_579))
      | ~ v1_funct_1(C_578)
      | ~ l1_pre_topc(B_576)
      | ~ v2_pre_topc(B_576)
      | v2_struct_0(B_576)
      | ~ l1_pre_topc(A_579)
      | ~ v2_pre_topc(A_579)
      | v2_struct_0(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1331,plain,(
    ! [D_580,F_577] :
      ( r1_tmap_1(D_580,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_580),F_577)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_577)
      | ~ m1_subset_1(F_577,u1_struct_0(D_580))
      | ~ m1_subset_1(F_577,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_580,'#skF_4')
      | v2_struct_0(D_580)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1329])).

tff(c_1334,plain,(
    ! [D_580,F_577] :
      ( r1_tmap_1(D_580,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_580),F_577)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_577)
      | ~ m1_subset_1(F_577,u1_struct_0(D_580))
      | ~ m1_subset_1(F_577,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_580,'#skF_4')
      | v2_struct_0(D_580)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_1331])).

tff(c_1490,plain,(
    ! [D_605,F_606] :
      ( r1_tmap_1(D_605,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_605),F_606)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_606)
      | ~ m1_subset_1(F_606,u1_struct_0(D_605))
      | ~ m1_subset_1(F_606,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_605,'#skF_4')
      | v2_struct_0(D_605) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_1334])).

tff(c_985,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1495,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1490,c_985])).

tff(c_1502,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_77,c_986,c_1495])).

tff(c_1504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:05:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.76  
% 4.39/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.77  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.39/1.77  
% 4.39/1.77  %Foreground sorts:
% 4.39/1.77  
% 4.39/1.77  
% 4.39/1.77  %Background operators:
% 4.39/1.77  
% 4.39/1.77  
% 4.39/1.77  %Foreground operators:
% 4.39/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.39/1.77  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.39/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.39/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.39/1.77  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.39/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.77  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.39/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.39/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.39/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.39/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.39/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.39/1.77  tff('#skF_9', type, '#skF_9': $i).
% 4.39/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.39/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.39/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.39/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.39/1.77  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.39/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.39/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.39/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.77  
% 4.39/1.79  tff(f_236, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 4.39/1.79  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.39/1.79  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.39/1.79  tff(f_39, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.39/1.79  tff(f_186, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.39/1.79  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.39/1.79  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.39/1.79  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_46, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_32, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_40, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_77, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 4.39/1.79  tff(c_34, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_24, plain, (![B_43, A_41]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_pre_topc(B_43, A_41) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.39/1.79  tff(c_38, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_36, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_311, plain, (![C_428, A_429, B_430, D_431]: (m1_connsp_2(C_428, A_429, B_430) | ~r2_hidden(B_430, D_431) | ~r1_tarski(D_431, C_428) | ~v3_pre_topc(D_431, A_429) | ~m1_subset_1(D_431, k1_zfmisc_1(u1_struct_0(A_429))) | ~m1_subset_1(C_428, k1_zfmisc_1(u1_struct_0(A_429))) | ~m1_subset_1(B_430, u1_struct_0(A_429)) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.39/1.79  tff(c_324, plain, (![C_432, A_433]: (m1_connsp_2(C_432, A_433, '#skF_8') | ~r1_tarski('#skF_7', C_432) | ~v3_pre_topc('#skF_7', A_433) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_433))) | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0(A_433))) | ~m1_subset_1('#skF_8', u1_struct_0(A_433)) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(resolution, [status(thm)], [c_36, c_311])).
% 4.39/1.79  tff(c_326, plain, (![C_432]: (m1_connsp_2(C_432, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_432) | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_324])).
% 4.39/1.79  tff(c_329, plain, (![C_432]: (m1_connsp_2(C_432, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_38, c_326])).
% 4.39/1.79  tff(c_338, plain, (![C_439]: (m1_connsp_2(C_439, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_329])).
% 4.39/1.79  tff(c_360, plain, (![B_43]: (m1_connsp_2(u1_struct_0(B_43), '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(B_43)) | ~m1_pre_topc(B_43, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_338])).
% 4.39/1.79  tff(c_420, plain, (![B_442]: (m1_connsp_2(u1_struct_0(B_442), '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(B_442)) | ~m1_pre_topc(B_442, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_360])).
% 4.39/1.79  tff(c_2, plain, (![C_4, A_1, B_2]: (m1_subset_1(C_4, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_connsp_2(C_4, A_1, B_2) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.39/1.79  tff(c_422, plain, (![B_442]: (m1_subset_1(u1_struct_0(B_442), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski('#skF_7', u1_struct_0(B_442)) | ~m1_pre_topc(B_442, '#skF_4'))), inference(resolution, [status(thm)], [c_420, c_2])).
% 4.39/1.79  tff(c_425, plain, (![B_442]: (m1_subset_1(u1_struct_0(B_442), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~r1_tarski('#skF_7', u1_struct_0(B_442)) | ~m1_pre_topc(B_442, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_422])).
% 4.39/1.79  tff(c_426, plain, (![B_442]: (m1_subset_1(u1_struct_0(B_442), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_7', u1_struct_0(B_442)) | ~m1_pre_topc(B_442, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_425])).
% 4.39/1.79  tff(c_87, plain, (![A_362, B_363, C_364]: (r1_tarski('#skF_2'(A_362, B_363, C_364), C_364) | ~m1_connsp_2(C_364, A_362, B_363) | ~m1_subset_1(C_364, k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_subset_1(B_363, u1_struct_0(A_362)) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.39/1.79  tff(c_92, plain, (![A_41, B_363, B_43]: (r1_tarski('#skF_2'(A_41, B_363, u1_struct_0(B_43)), u1_struct_0(B_43)) | ~m1_connsp_2(u1_struct_0(B_43), A_41, B_363) | ~m1_subset_1(B_363, u1_struct_0(A_41)) | ~v2_pre_topc(A_41) | v2_struct_0(A_41) | ~m1_pre_topc(B_43, A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_24, c_87])).
% 4.39/1.79  tff(c_22, plain, (![A_19, B_31, C_37]: (m1_subset_1('#skF_2'(A_19, B_31, C_37), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_connsp_2(C_37, A_19, B_31) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_31, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.39/1.79  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_68, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_76, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 4.39/1.79  tff(c_83, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_76])).
% 4.39/1.79  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_74, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.39/1.79  tff(c_75, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 4.39/1.79  tff(c_84, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_83, c_75])).
% 4.39/1.79  tff(c_529, plain, (![B_449, D_447, E_452, C_448, G_450, A_451]: (r1_tmap_1(B_449, A_451, C_448, G_450) | ~r1_tmap_1(D_447, A_451, k2_tmap_1(B_449, A_451, C_448, D_447), G_450) | ~m1_connsp_2(E_452, B_449, G_450) | ~r1_tarski(E_452, u1_struct_0(D_447)) | ~m1_subset_1(G_450, u1_struct_0(D_447)) | ~m1_subset_1(G_450, u1_struct_0(B_449)) | ~m1_subset_1(E_452, k1_zfmisc_1(u1_struct_0(B_449))) | ~m1_pre_topc(D_447, B_449) | v2_struct_0(D_447) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_449), u1_struct_0(A_451)))) | ~v1_funct_2(C_448, u1_struct_0(B_449), u1_struct_0(A_451)) | ~v1_funct_1(C_448) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | v2_struct_0(B_449) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.39/1.79  tff(c_531, plain, (![E_452]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_452, '#skF_4', '#skF_8') | ~r1_tarski(E_452, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_452, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_84, c_529])).
% 4.39/1.79  tff(c_534, plain, (![E_452]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_452, '#skF_4', '#skF_8') | ~r1_tarski(E_452, u1_struct_0('#skF_6')) | ~m1_subset_1(E_452, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_50, c_46, c_42, c_77, c_531])).
% 4.39/1.79  tff(c_536, plain, (![E_453]: (~m1_connsp_2(E_453, '#skF_4', '#skF_8') | ~r1_tarski(E_453, u1_struct_0('#skF_6')) | ~m1_subset_1(E_453, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_48, c_83, c_534])).
% 4.39/1.79  tff(c_557, plain, (![B_31, C_37]: (~m1_connsp_2('#skF_2'('#skF_4', B_31, C_37), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_31, C_37), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_37, '#skF_4', B_31) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_31, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_536])).
% 4.39/1.79  tff(c_581, plain, (![B_31, C_37]: (~m1_connsp_2('#skF_2'('#skF_4', B_31, C_37), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_31, C_37), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_37, '#skF_4', B_31) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_31, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_557])).
% 4.39/1.79  tff(c_708, plain, (![B_474, C_475]: (~m1_connsp_2('#skF_2'('#skF_4', B_474, C_475), '#skF_4', '#skF_8') | ~r1_tarski('#skF_2'('#skF_4', B_474, C_475), u1_struct_0('#skF_6')) | ~m1_connsp_2(C_475, '#skF_4', B_474) | ~m1_subset_1(C_475, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_474, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_581])).
% 4.39/1.79  tff(c_716, plain, (![B_363]: (~m1_connsp_2('#skF_2'('#skF_4', B_363, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_363) | ~m1_subset_1(B_363, u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_708])).
% 4.39/1.79  tff(c_722, plain, (![B_363]: (~m1_connsp_2('#skF_2'('#skF_4', B_363, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_363) | ~m1_subset_1(B_363, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_58, c_716])).
% 4.39/1.79  tff(c_723, plain, (![B_363]: (~m1_connsp_2('#skF_2'('#skF_4', B_363, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_363) | ~m1_subset_1(B_363, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_722])).
% 4.39/1.79  tff(c_724, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_723])).
% 4.39/1.79  tff(c_727, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_426, c_724])).
% 4.39/1.79  tff(c_734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_727])).
% 4.39/1.79  tff(c_736, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_723])).
% 4.39/1.79  tff(c_330, plain, (![C_432]: (m1_connsp_2(C_432, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_329])).
% 4.39/1.79  tff(c_746, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_736, c_330])).
% 4.39/1.79  tff(c_764, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_746])).
% 4.39/1.79  tff(c_8, plain, (![A_5, B_13, C_17]: (m1_connsp_2('#skF_1'(A_5, B_13, C_17), A_5, B_13) | ~m1_connsp_2(C_17, A_5, B_13) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_13, u1_struct_0(A_5)) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.39/1.79  tff(c_748, plain, (![B_13]: (m1_connsp_2('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), '#skF_4', B_13) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_736, c_8])).
% 4.39/1.79  tff(c_767, plain, (![B_13]: (m1_connsp_2('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), '#skF_4', B_13) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_748])).
% 4.39/1.79  tff(c_768, plain, (![B_13]: (m1_connsp_2('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), '#skF_4', B_13) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_767])).
% 4.39/1.79  tff(c_4, plain, (![A_5, B_13, C_17]: (r1_tarski('#skF_1'(A_5, B_13, C_17), C_17) | ~m1_connsp_2(C_17, A_5, B_13) | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_13, u1_struct_0(A_5)) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.39/1.79  tff(c_752, plain, (![B_13]: (r1_tarski('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_736, c_4])).
% 4.39/1.79  tff(c_775, plain, (![B_13]: (r1_tarski('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_752])).
% 4.39/1.79  tff(c_776, plain, (![B_13]: (r1_tarski('#skF_1'('#skF_4', B_13, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_13) | ~m1_subset_1(B_13, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_775])).
% 4.39/1.79  tff(c_813, plain, (![B_486]: (m1_connsp_2('#skF_1'('#skF_4', B_486, u1_struct_0('#skF_6')), '#skF_4', B_486) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_486) | ~m1_subset_1(B_486, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_767])).
% 4.39/1.79  tff(c_815, plain, (![B_486]: (m1_subset_1('#skF_1'('#skF_4', B_486, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_486) | ~m1_subset_1(B_486, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_813, c_2])).
% 4.39/1.79  tff(c_818, plain, (![B_486]: (m1_subset_1('#skF_1'('#skF_4', B_486, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_486) | ~m1_subset_1(B_486, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_815])).
% 4.39/1.79  tff(c_820, plain, (![B_487]: (m1_subset_1('#skF_1'('#skF_4', B_487, u1_struct_0('#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_487) | ~m1_subset_1(B_487, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_818])).
% 4.39/1.79  tff(c_535, plain, (![E_452]: (~m1_connsp_2(E_452, '#skF_4', '#skF_8') | ~r1_tarski(E_452, u1_struct_0('#skF_6')) | ~m1_subset_1(E_452, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_48, c_83, c_534])).
% 4.39/1.79  tff(c_944, plain, (![B_496]: (~m1_connsp_2('#skF_1'('#skF_4', B_496, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_496, u1_struct_0('#skF_6')), u1_struct_0('#skF_6')) | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_496) | ~m1_subset_1(B_496, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_820, c_535])).
% 4.39/1.79  tff(c_964, plain, (![B_497]: (~m1_connsp_2('#skF_1'('#skF_4', B_497, u1_struct_0('#skF_6')), '#skF_4', '#skF_8') | ~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', B_497) | ~m1_subset_1(B_497, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_776, c_944])).
% 4.39/1.79  tff(c_971, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_768, c_964])).
% 4.39/1.79  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_764, c_971])).
% 4.39/1.79  tff(c_986, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_76])).
% 4.39/1.79  tff(c_1329, plain, (![B_576, A_579, D_580, F_577, C_578]: (r1_tmap_1(D_580, A_579, k2_tmap_1(B_576, A_579, C_578, D_580), F_577) | ~r1_tmap_1(B_576, A_579, C_578, F_577) | ~m1_subset_1(F_577, u1_struct_0(D_580)) | ~m1_subset_1(F_577, u1_struct_0(B_576)) | ~m1_pre_topc(D_580, B_576) | v2_struct_0(D_580) | ~m1_subset_1(C_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_576), u1_struct_0(A_579)))) | ~v1_funct_2(C_578, u1_struct_0(B_576), u1_struct_0(A_579)) | ~v1_funct_1(C_578) | ~l1_pre_topc(B_576) | ~v2_pre_topc(B_576) | v2_struct_0(B_576) | ~l1_pre_topc(A_579) | ~v2_pre_topc(A_579) | v2_struct_0(A_579))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.39/1.79  tff(c_1331, plain, (![D_580, F_577]: (r1_tmap_1(D_580, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_580), F_577) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_577) | ~m1_subset_1(F_577, u1_struct_0(D_580)) | ~m1_subset_1(F_577, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_580, '#skF_4') | v2_struct_0(D_580) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_1329])).
% 4.39/1.79  tff(c_1334, plain, (![D_580, F_577]: (r1_tmap_1(D_580, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_580), F_577) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_577) | ~m1_subset_1(F_577, u1_struct_0(D_580)) | ~m1_subset_1(F_577, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_580, '#skF_4') | v2_struct_0(D_580) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_1331])).
% 4.39/1.79  tff(c_1490, plain, (![D_605, F_606]: (r1_tmap_1(D_605, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_605), F_606) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_606) | ~m1_subset_1(F_606, u1_struct_0(D_605)) | ~m1_subset_1(F_606, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_605, '#skF_4') | v2_struct_0(D_605))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_1334])).
% 4.39/1.79  tff(c_985, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_76])).
% 4.39/1.79  tff(c_1495, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1490, c_985])).
% 4.39/1.79  tff(c_1502, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_77, c_986, c_1495])).
% 4.39/1.79  tff(c_1504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1502])).
% 4.39/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.79  
% 4.39/1.79  Inference rules
% 4.39/1.79  ----------------------
% 4.39/1.79  #Ref     : 0
% 4.39/1.79  #Sup     : 263
% 4.39/1.79  #Fact    : 0
% 4.39/1.79  #Define  : 0
% 4.39/1.79  #Split   : 4
% 4.39/1.79  #Chain   : 0
% 4.39/1.79  #Close   : 0
% 4.39/1.79  
% 4.39/1.79  Ordering : KBO
% 4.39/1.79  
% 4.39/1.79  Simplification rules
% 4.39/1.79  ----------------------
% 4.39/1.79  #Subsume      : 19
% 4.39/1.79  #Demod        : 330
% 4.39/1.79  #Tautology    : 8
% 4.39/1.79  #SimpNegUnit  : 133
% 4.39/1.79  #BackRed      : 0
% 4.39/1.79  
% 4.39/1.79  #Partial instantiations: 0
% 4.39/1.79  #Strategies tried      : 1
% 4.39/1.79  
% 4.39/1.79  Timing (in seconds)
% 4.39/1.79  ----------------------
% 4.39/1.79  Preprocessing        : 0.40
% 4.39/1.79  Parsing              : 0.20
% 4.39/1.79  CNF conversion       : 0.06
% 4.39/1.79  Main loop            : 0.61
% 4.39/1.79  Inferencing          : 0.22
% 4.39/1.79  Reduction            : 0.20
% 4.39/1.80  Demodulation         : 0.14
% 4.39/1.80  BG Simplification    : 0.03
% 4.39/1.80  Subsumption          : 0.12
% 4.39/1.80  Abstraction          : 0.03
% 4.76/1.80  MUC search           : 0.00
% 4.76/1.80  Cooper               : 0.00
% 4.76/1.80  Total                : 1.05
% 4.76/1.80  Index Insertion      : 0.00
% 4.76/1.80  Index Deletion       : 0.00
% 4.76/1.80  Index Matching       : 0.00
% 4.76/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
