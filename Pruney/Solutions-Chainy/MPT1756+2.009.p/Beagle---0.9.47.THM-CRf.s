%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 206 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  301 (1576 expanded)
%              Number of equality atoms :    3 (  70 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
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

tff(f_103,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_22,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_67,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_24,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_277,B_278] :
      ( ~ r2_hidden('#skF_1'(A_277,B_278),B_278)
      | r1_tarski(A_277,B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_28,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_26,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_412,plain,(
    ! [C_361,A_362,B_363,D_364] :
      ( m1_connsp_2(C_361,A_362,B_363)
      | ~ r2_hidden(B_363,D_364)
      | ~ r1_tarski(D_364,C_361)
      | ~ v3_pre_topc(D_364,A_362)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_subset_1(C_361,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_subset_1(B_363,u1_struct_0(A_362))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_492,plain,(
    ! [C_373,A_374] :
      ( m1_connsp_2(C_373,A_374,'#skF_8')
      | ~ r1_tarski('#skF_7',C_373)
      | ~ v3_pre_topc('#skF_7',A_374)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1(C_373,k1_zfmisc_1(u1_struct_0(A_374)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_374))
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_26,c_412])).

tff(c_494,plain,(
    ! [C_373] :
      ( m1_connsp_2(C_373,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_373)
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(C_373,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_492])).

tff(c_497,plain,(
    ! [C_373] :
      ( m1_connsp_2(C_373,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_28,c_494])).

tff(c_499,plain,(
    ! [C_375] :
      ( m1_connsp_2(C_375,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_497])).

tff(c_506,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_499])).

tff(c_513,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_506])).

tff(c_64,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_73,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_58])).

tff(c_93,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_66])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_559,plain,(
    ! [D_387,B_386,A_385,E_389,G_384,C_388] :
      ( r1_tmap_1(B_386,A_385,C_388,G_384)
      | ~ r1_tmap_1(D_387,A_385,k2_tmap_1(B_386,A_385,C_388,D_387),G_384)
      | ~ m1_connsp_2(E_389,B_386,G_384)
      | ~ r1_tarski(E_389,u1_struct_0(D_387))
      | ~ m1_subset_1(G_384,u1_struct_0(D_387))
      | ~ m1_subset_1(G_384,u1_struct_0(B_386))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0(B_386)))
      | ~ m1_pre_topc(D_387,B_386)
      | v2_struct_0(D_387)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386),u1_struct_0(A_385))))
      | ~ v1_funct_2(C_388,u1_struct_0(B_386),u1_struct_0(A_385))
      | ~ v1_funct_1(C_388)
      | ~ l1_pre_topc(B_386)
      | ~ v2_pre_topc(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_561,plain,(
    ! [E_389] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_389,'#skF_4','#skF_8')
      | ~ r1_tarski(E_389,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_73,c_559])).

tff(c_564,plain,(
    ! [E_389] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_389,'#skF_4','#skF_8')
      | ~ r1_tarski(E_389,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_44,c_42,c_40,c_36,c_32,c_67,c_561])).

tff(c_566,plain,(
    ! [E_390] :
      ( ~ m1_connsp_2(E_390,'#skF_4','#skF_8')
      | ~ r1_tarski(E_390,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_390,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_93,c_564])).

tff(c_573,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_566])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_513,c_573])).

tff(c_582,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_584,plain,(
    ! [A_391,B_392] :
      ( ~ r2_hidden('#skF_1'(A_391,B_392),B_392)
      | r1_tarski(A_391,B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_589,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_584])).

tff(c_852,plain,(
    ! [C_456,A_457,B_458,D_459] :
      ( m1_connsp_2(C_456,A_457,B_458)
      | ~ r2_hidden(B_458,D_459)
      | ~ r1_tarski(D_459,C_456)
      | ~ v3_pre_topc(D_459,A_457)
      | ~ m1_subset_1(D_459,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ m1_subset_1(C_456,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ m1_subset_1(B_458,u1_struct_0(A_457))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_928,plain,(
    ! [C_468,A_469] :
      ( m1_connsp_2(C_468,A_469,'#skF_8')
      | ~ r1_tarski('#skF_7',C_468)
      | ~ v3_pre_topc('#skF_7',A_469)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ m1_subset_1(C_468,k1_zfmisc_1(u1_struct_0(A_469)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_469))
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(resolution,[status(thm)],[c_26,c_852])).

tff(c_930,plain,(
    ! [C_468] :
      ( m1_connsp_2(C_468,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_468)
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(C_468,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_928])).

tff(c_933,plain,(
    ! [C_468] :
      ( m1_connsp_2(C_468,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_28,c_930])).

tff(c_935,plain,(
    ! [C_470] :
      ( m1_connsp_2(C_470,'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_7',C_470)
      | ~ m1_subset_1(C_470,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_933])).

tff(c_942,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_935])).

tff(c_949,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_942])).

tff(c_1073,plain,(
    ! [E_512,C_511,D_510,G_507,A_508,B_509] :
      ( r1_tmap_1(D_510,A_508,k2_tmap_1(B_509,A_508,C_511,D_510),G_507)
      | ~ r1_tmap_1(B_509,A_508,C_511,G_507)
      | ~ m1_connsp_2(E_512,B_509,G_507)
      | ~ r1_tarski(E_512,u1_struct_0(D_510))
      | ~ m1_subset_1(G_507,u1_struct_0(D_510))
      | ~ m1_subset_1(G_507,u1_struct_0(B_509))
      | ~ m1_subset_1(E_512,k1_zfmisc_1(u1_struct_0(B_509)))
      | ~ m1_pre_topc(D_510,B_509)
      | v2_struct_0(D_510)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_509),u1_struct_0(A_508))))
      | ~ v1_funct_2(C_511,u1_struct_0(B_509),u1_struct_0(A_508))
      | ~ v1_funct_1(C_511)
      | ~ l1_pre_topc(B_509)
      | ~ v2_pre_topc(B_509)
      | v2_struct_0(B_509)
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1079,plain,(
    ! [D_510,A_508,C_511] :
      ( r1_tmap_1(D_510,A_508,k2_tmap_1('#skF_4',A_508,C_511,D_510),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_508,C_511,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_510))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_510))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_510,'#skF_4')
      | v2_struct_0(D_510)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_508))))
      | ~ v1_funct_2(C_511,u1_struct_0('#skF_4'),u1_struct_0(A_508))
      | ~ v1_funct_1(C_511)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_949,c_1073])).

tff(c_1090,plain,(
    ! [D_510,A_508,C_511] :
      ( r1_tmap_1(D_510,A_508,k2_tmap_1('#skF_4',A_508,C_511,D_510),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_508,C_511,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_510))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_510))
      | ~ m1_pre_topc(D_510,'#skF_4')
      | v2_struct_0(D_510)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_508))))
      | ~ v1_funct_2(C_511,u1_struct_0('#skF_4'),u1_struct_0(A_508))
      | ~ v1_funct_1(C_511)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_32,c_1079])).

tff(c_1841,plain,(
    ! [D_671,A_672,C_673] :
      ( r1_tmap_1(D_671,A_672,k2_tmap_1('#skF_4',A_672,C_673,D_671),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_672,C_673,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_671))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_671))
      | ~ m1_pre_topc(D_671,'#skF_4')
      | v2_struct_0(D_671)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_672))))
      | ~ v1_funct_2(C_673,u1_struct_0('#skF_4'),u1_struct_0(A_672))
      | ~ v1_funct_1(C_673)
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672)
      | v2_struct_0(A_672) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1090])).

tff(c_1843,plain,(
    ! [D_671] :
      ( r1_tmap_1(D_671,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_671),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_671))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_671))
      | ~ m1_pre_topc(D_671,'#skF_4')
      | v2_struct_0(D_671)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_1841])).

tff(c_1846,plain,(
    ! [D_671] :
      ( r1_tmap_1(D_671,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_671),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_671))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_671))
      | ~ m1_pre_topc(D_671,'#skF_4')
      | v2_struct_0(D_671)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44,c_42,c_582,c_1843])).

tff(c_1848,plain,(
    ! [D_674] :
      ( r1_tmap_1(D_674,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_674),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_674))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_674))
      | ~ m1_pre_topc(D_674,'#skF_4')
      | v2_struct_0(D_674) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1846])).

tff(c_591,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_66])).

tff(c_1853,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1848,c_591])).

tff(c_1860,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_67,c_24,c_1853])).

tff(c_1862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1860])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.06  
% 5.25/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.06  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 5.58/2.06  
% 5.58/2.06  %Foreground sorts:
% 5.58/2.06  
% 5.58/2.06  
% 5.58/2.06  %Background operators:
% 5.58/2.06  
% 5.58/2.06  
% 5.58/2.06  %Foreground operators:
% 5.58/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.58/2.06  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.58/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.58/2.06  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.58/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.58/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.58/2.06  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.58/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.58/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.58/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.58/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.58/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.58/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.58/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.58/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.58/2.06  tff('#skF_9', type, '#skF_9': $i).
% 5.58/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.58/2.06  tff('#skF_8', type, '#skF_8': $i).
% 5.58/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.58/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.58/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.58/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.58/2.06  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.58/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.58/2.06  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.58/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.58/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.58/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.58/2.06  
% 5.67/2.08  tff(f_153, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 5.67/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.67/2.08  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.67/2.08  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.67/2.08  tff(c_38, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_36, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_22, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_30, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_67, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 5.67/2.08  tff(c_24, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.08  tff(c_74, plain, (![A_277, B_278]: (~r2_hidden('#skF_1'(A_277, B_278), B_278) | r1_tarski(A_277, B_278))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.08  tff(c_79, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_74])).
% 5.67/2.08  tff(c_34, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_28, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_26, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_412, plain, (![C_361, A_362, B_363, D_364]: (m1_connsp_2(C_361, A_362, B_363) | ~r2_hidden(B_363, D_364) | ~r1_tarski(D_364, C_361) | ~v3_pre_topc(D_364, A_362) | ~m1_subset_1(D_364, k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_subset_1(C_361, k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_subset_1(B_363, u1_struct_0(A_362)) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.67/2.08  tff(c_492, plain, (![C_373, A_374]: (m1_connsp_2(C_373, A_374, '#skF_8') | ~r1_tarski('#skF_7', C_373) | ~v3_pre_topc('#skF_7', A_374) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1(C_373, k1_zfmisc_1(u1_struct_0(A_374))) | ~m1_subset_1('#skF_8', u1_struct_0(A_374)) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(resolution, [status(thm)], [c_26, c_412])).
% 5.67/2.08  tff(c_494, plain, (![C_373]: (m1_connsp_2(C_373, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_373) | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(C_373, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_492])).
% 5.67/2.08  tff(c_497, plain, (![C_373]: (m1_connsp_2(C_373, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_28, c_494])).
% 5.67/2.08  tff(c_499, plain, (![C_375]: (m1_connsp_2(C_375, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_497])).
% 5.67/2.08  tff(c_506, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_499])).
% 5.67/2.08  tff(c_513, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_506])).
% 5.67/2.08  tff(c_64, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_65, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_64])).
% 5.67/2.08  tff(c_73, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_65])).
% 5.67/2.08  tff(c_58, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_66, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_58])).
% 5.67/2.08  tff(c_93, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_66])).
% 5.67/2.08  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.67/2.08  tff(c_559, plain, (![D_387, B_386, A_385, E_389, G_384, C_388]: (r1_tmap_1(B_386, A_385, C_388, G_384) | ~r1_tmap_1(D_387, A_385, k2_tmap_1(B_386, A_385, C_388, D_387), G_384) | ~m1_connsp_2(E_389, B_386, G_384) | ~r1_tarski(E_389, u1_struct_0(D_387)) | ~m1_subset_1(G_384, u1_struct_0(D_387)) | ~m1_subset_1(G_384, u1_struct_0(B_386)) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0(B_386))) | ~m1_pre_topc(D_387, B_386) | v2_struct_0(D_387) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386), u1_struct_0(A_385)))) | ~v1_funct_2(C_388, u1_struct_0(B_386), u1_struct_0(A_385)) | ~v1_funct_1(C_388) | ~l1_pre_topc(B_386) | ~v2_pre_topc(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.67/2.08  tff(c_561, plain, (![E_389]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_389, '#skF_4', '#skF_8') | ~r1_tarski(E_389, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_73, c_559])).
% 5.67/2.08  tff(c_564, plain, (![E_389]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_389, '#skF_4', '#skF_8') | ~r1_tarski(E_389, u1_struct_0('#skF_6')) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_46, c_44, c_42, c_40, c_36, c_32, c_67, c_561])).
% 5.67/2.08  tff(c_566, plain, (![E_390]: (~m1_connsp_2(E_390, '#skF_4', '#skF_8') | ~r1_tarski(E_390, u1_struct_0('#skF_6')) | ~m1_subset_1(E_390, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_38, c_93, c_564])).
% 5.67/2.08  tff(c_573, plain, (~m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_566])).
% 5.67/2.08  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_513, c_573])).
% 5.67/2.08  tff(c_582, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_65])).
% 5.67/2.08  tff(c_584, plain, (![A_391, B_392]: (~r2_hidden('#skF_1'(A_391, B_392), B_392) | r1_tarski(A_391, B_392))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.08  tff(c_589, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_584])).
% 5.67/2.08  tff(c_852, plain, (![C_456, A_457, B_458, D_459]: (m1_connsp_2(C_456, A_457, B_458) | ~r2_hidden(B_458, D_459) | ~r1_tarski(D_459, C_456) | ~v3_pre_topc(D_459, A_457) | ~m1_subset_1(D_459, k1_zfmisc_1(u1_struct_0(A_457))) | ~m1_subset_1(C_456, k1_zfmisc_1(u1_struct_0(A_457))) | ~m1_subset_1(B_458, u1_struct_0(A_457)) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.67/2.08  tff(c_928, plain, (![C_468, A_469]: (m1_connsp_2(C_468, A_469, '#skF_8') | ~r1_tarski('#skF_7', C_468) | ~v3_pre_topc('#skF_7', A_469) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_469))) | ~m1_subset_1(C_468, k1_zfmisc_1(u1_struct_0(A_469))) | ~m1_subset_1('#skF_8', u1_struct_0(A_469)) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(resolution, [status(thm)], [c_26, c_852])).
% 5.67/2.08  tff(c_930, plain, (![C_468]: (m1_connsp_2(C_468, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_468) | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(C_468, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_928])).
% 5.67/2.08  tff(c_933, plain, (![C_468]: (m1_connsp_2(C_468, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_28, c_930])).
% 5.67/2.08  tff(c_935, plain, (![C_470]: (m1_connsp_2(C_470, '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', C_470) | ~m1_subset_1(C_470, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_933])).
% 5.67/2.08  tff(c_942, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_935])).
% 5.67/2.08  tff(c_949, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_942])).
% 5.67/2.08  tff(c_1073, plain, (![E_512, C_511, D_510, G_507, A_508, B_509]: (r1_tmap_1(D_510, A_508, k2_tmap_1(B_509, A_508, C_511, D_510), G_507) | ~r1_tmap_1(B_509, A_508, C_511, G_507) | ~m1_connsp_2(E_512, B_509, G_507) | ~r1_tarski(E_512, u1_struct_0(D_510)) | ~m1_subset_1(G_507, u1_struct_0(D_510)) | ~m1_subset_1(G_507, u1_struct_0(B_509)) | ~m1_subset_1(E_512, k1_zfmisc_1(u1_struct_0(B_509))) | ~m1_pre_topc(D_510, B_509) | v2_struct_0(D_510) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_509), u1_struct_0(A_508)))) | ~v1_funct_2(C_511, u1_struct_0(B_509), u1_struct_0(A_508)) | ~v1_funct_1(C_511) | ~l1_pre_topc(B_509) | ~v2_pre_topc(B_509) | v2_struct_0(B_509) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.67/2.08  tff(c_1079, plain, (![D_510, A_508, C_511]: (r1_tmap_1(D_510, A_508, k2_tmap_1('#skF_4', A_508, C_511, D_510), '#skF_8') | ~r1_tmap_1('#skF_4', A_508, C_511, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_510)) | ~m1_subset_1('#skF_8', u1_struct_0(D_510)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_510, '#skF_4') | v2_struct_0(D_510) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_508)))) | ~v1_funct_2(C_511, u1_struct_0('#skF_4'), u1_struct_0(A_508)) | ~v1_funct_1(C_511) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(resolution, [status(thm)], [c_949, c_1073])).
% 5.67/2.08  tff(c_1090, plain, (![D_510, A_508, C_511]: (r1_tmap_1(D_510, A_508, k2_tmap_1('#skF_4', A_508, C_511, D_510), '#skF_8') | ~r1_tmap_1('#skF_4', A_508, C_511, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_510)) | ~m1_subset_1('#skF_8', u1_struct_0(D_510)) | ~m1_pre_topc(D_510, '#skF_4') | v2_struct_0(D_510) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_508)))) | ~v1_funct_2(C_511, u1_struct_0('#skF_4'), u1_struct_0(A_508)) | ~v1_funct_1(C_511) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_32, c_1079])).
% 5.67/2.08  tff(c_1841, plain, (![D_671, A_672, C_673]: (r1_tmap_1(D_671, A_672, k2_tmap_1('#skF_4', A_672, C_673, D_671), '#skF_8') | ~r1_tmap_1('#skF_4', A_672, C_673, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_671)) | ~m1_subset_1('#skF_8', u1_struct_0(D_671)) | ~m1_pre_topc(D_671, '#skF_4') | v2_struct_0(D_671) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_672)))) | ~v1_funct_2(C_673, u1_struct_0('#skF_4'), u1_struct_0(A_672)) | ~v1_funct_1(C_673) | ~l1_pre_topc(A_672) | ~v2_pre_topc(A_672) | v2_struct_0(A_672))), inference(negUnitSimplification, [status(thm)], [c_50, c_1090])).
% 5.67/2.08  tff(c_1843, plain, (![D_671]: (r1_tmap_1(D_671, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_671), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_671)) | ~m1_subset_1('#skF_8', u1_struct_0(D_671)) | ~m1_pre_topc(D_671, '#skF_4') | v2_struct_0(D_671) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_1841])).
% 5.67/2.08  tff(c_1846, plain, (![D_671]: (r1_tmap_1(D_671, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_671), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_671)) | ~m1_subset_1('#skF_8', u1_struct_0(D_671)) | ~m1_pre_topc(D_671, '#skF_4') | v2_struct_0(D_671) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44, c_42, c_582, c_1843])).
% 5.67/2.08  tff(c_1848, plain, (![D_674]: (r1_tmap_1(D_674, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_674), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_674)) | ~m1_subset_1('#skF_8', u1_struct_0(D_674)) | ~m1_pre_topc(D_674, '#skF_4') | v2_struct_0(D_674))), inference(negUnitSimplification, [status(thm)], [c_56, c_1846])).
% 5.67/2.08  tff(c_591, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_66])).
% 5.67/2.08  tff(c_1853, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1848, c_591])).
% 5.67/2.08  tff(c_1860, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_67, c_24, c_1853])).
% 5.67/2.08  tff(c_1862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1860])).
% 5.67/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.08  
% 5.67/2.08  Inference rules
% 5.67/2.08  ----------------------
% 5.67/2.08  #Ref     : 0
% 5.67/2.08  #Sup     : 406
% 5.67/2.08  #Fact    : 0
% 5.67/2.08  #Define  : 0
% 5.67/2.08  #Split   : 4
% 5.67/2.08  #Chain   : 0
% 5.67/2.08  #Close   : 0
% 5.67/2.08  
% 5.67/2.08  Ordering : KBO
% 5.67/2.08  
% 5.67/2.08  Simplification rules
% 5.67/2.08  ----------------------
% 5.67/2.08  #Subsume      : 158
% 5.67/2.08  #Demod        : 231
% 5.67/2.08  #Tautology    : 27
% 5.67/2.08  #SimpNegUnit  : 61
% 5.67/2.08  #BackRed      : 0
% 5.67/2.08  
% 5.67/2.08  #Partial instantiations: 0
% 5.67/2.08  #Strategies tried      : 1
% 5.67/2.08  
% 5.67/2.08  Timing (in seconds)
% 5.67/2.08  ----------------------
% 5.67/2.08  Preprocessing        : 0.37
% 5.67/2.08  Parsing              : 0.19
% 5.67/2.08  CNF conversion       : 0.05
% 5.67/2.08  Main loop            : 0.89
% 5.67/2.08  Inferencing          : 0.29
% 5.67/2.08  Reduction            : 0.24
% 5.67/2.08  Demodulation         : 0.16
% 5.67/2.08  BG Simplification    : 0.03
% 5.67/2.08  Subsumption          : 0.28
% 5.67/2.08  Abstraction          : 0.03
% 5.67/2.08  MUC search           : 0.00
% 5.67/2.08  Cooper               : 0.00
% 5.67/2.08  Total                : 1.30
% 5.67/2.08  Index Insertion      : 0.00
% 5.67/2.08  Index Deletion       : 0.00
% 5.67/2.08  Index Matching       : 0.00
% 5.67/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
