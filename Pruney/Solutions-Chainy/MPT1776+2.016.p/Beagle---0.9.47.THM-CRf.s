%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:32 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 184 expanded)
%              Number of leaves         :   30 (  87 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 (1528 expanded)
%              Number of equality atoms :    4 (  69 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_161,axiom,(
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

tff(f_111,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_20,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_16,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_18,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_60,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_89,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_63,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54])).

tff(c_91,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_63])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_26,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_69,plain,(
    ! [B_388,A_389] :
      ( l1_pre_topc(B_388)
      | ~ m1_pre_topc(B_388,A_389)
      | ~ l1_pre_topc(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_81,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_8,plain,(
    ! [B_13,A_11] :
      ( r1_tarski(u1_struct_0(B_13),u1_struct_0(A_11))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    ! [B_392,C_393,A_394] :
      ( v1_tsep_1(B_392,C_393)
      | ~ r1_tarski(u1_struct_0(B_392),u1_struct_0(C_393))
      | ~ m1_pre_topc(C_393,A_394)
      | v2_struct_0(C_393)
      | ~ m1_pre_topc(B_392,A_394)
      | ~ v1_tsep_1(B_392,A_394)
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    ! [B_398,A_399,A_400] :
      ( v1_tsep_1(B_398,A_399)
      | ~ m1_pre_topc(A_399,A_400)
      | v2_struct_0(A_399)
      | ~ m1_pre_topc(B_398,A_400)
      | ~ v1_tsep_1(B_398,A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | ~ m1_pre_topc(B_398,A_399)
      | ~ l1_pre_topc(A_399) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_102,plain,(
    ! [B_398] :
      ( v1_tsep_1(B_398,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_398,'#skF_2')
      | ~ v1_tsep_1(B_398,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_398,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_100])).

tff(c_109,plain,(
    ! [B_398] :
      ( v1_tsep_1(B_398,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_398,'#skF_2')
      | ~ v1_tsep_1(B_398,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_398,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_44,c_42,c_102])).

tff(c_119,plain,(
    ! [B_401] :
      ( v1_tsep_1(B_401,'#skF_4')
      | ~ m1_pre_topc(B_401,'#skF_2')
      | ~ v1_tsep_1(B_401,'#skF_2')
      | ~ m1_pre_topc(B_401,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_109])).

tff(c_122,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_125,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_38,c_122])).

tff(c_143,plain,(
    ! [C_412,A_416,D_413,B_417,E_415,G_414] :
      ( r1_tmap_1(D_413,B_417,E_415,G_414)
      | ~ r1_tmap_1(C_412,B_417,k3_tmap_1(A_416,B_417,D_413,C_412,E_415),G_414)
      | ~ m1_subset_1(G_414,u1_struct_0(C_412))
      | ~ m1_subset_1(G_414,u1_struct_0(D_413))
      | ~ m1_pre_topc(C_412,D_413)
      | ~ v1_tsep_1(C_412,D_413)
      | ~ m1_subset_1(E_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413),u1_struct_0(B_417))))
      | ~ v1_funct_2(E_415,u1_struct_0(D_413),u1_struct_0(B_417))
      | ~ v1_funct_1(E_415)
      | ~ m1_pre_topc(D_413,A_416)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(C_412,A_416)
      | v2_struct_0(C_412)
      | ~ l1_pre_topc(B_417)
      | ~ v2_pre_topc(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_147,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_143])).

tff(c_154,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_50,c_48,c_38,c_34,c_32,c_30,c_28,c_125,c_22,c_20,c_64,c_147])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_40,c_36,c_91,c_154])).

tff(c_157,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_208,plain,(
    ! [D_431,E_430,B_429,G_432,A_434,C_433] :
      ( r1_tmap_1(D_431,B_429,k3_tmap_1(A_434,B_429,C_433,D_431,E_430),G_432)
      | ~ r1_tmap_1(C_433,B_429,E_430,G_432)
      | ~ m1_pre_topc(D_431,C_433)
      | ~ m1_subset_1(G_432,u1_struct_0(D_431))
      | ~ m1_subset_1(G_432,u1_struct_0(C_433))
      | ~ m1_subset_1(E_430,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_433),u1_struct_0(B_429))))
      | ~ v1_funct_2(E_430,u1_struct_0(C_433),u1_struct_0(B_429))
      | ~ v1_funct_1(E_430)
      | ~ m1_pre_topc(D_431,A_434)
      | v2_struct_0(D_431)
      | ~ m1_pre_topc(C_433,A_434)
      | v2_struct_0(C_433)
      | ~ l1_pre_topc(B_429)
      | ~ v2_pre_topc(B_429)
      | v2_struct_0(B_429)
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_210,plain,(
    ! [D_431,A_434,G_432] :
      ( r1_tmap_1(D_431,'#skF_1',k3_tmap_1(A_434,'#skF_1','#skF_4',D_431,'#skF_5'),G_432)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_432)
      | ~ m1_pre_topc(D_431,'#skF_4')
      | ~ m1_subset_1(G_432,u1_struct_0(D_431))
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_431,A_434)
      | v2_struct_0(D_431)
      | ~ m1_pre_topc('#skF_4',A_434)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(resolution,[status(thm)],[c_28,c_208])).

tff(c_213,plain,(
    ! [D_431,A_434,G_432] :
      ( r1_tmap_1(D_431,'#skF_1',k3_tmap_1(A_434,'#skF_1','#skF_4',D_431,'#skF_5'),G_432)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_432)
      | ~ m1_pre_topc(D_431,'#skF_4')
      | ~ m1_subset_1(G_432,u1_struct_0(D_431))
      | ~ m1_subset_1(G_432,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_431,A_434)
      | v2_struct_0(D_431)
      | ~ m1_pre_topc('#skF_4',A_434)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_434)
      | ~ v2_pre_topc(A_434)
      | v2_struct_0(A_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_32,c_30,c_210])).

tff(c_215,plain,(
    ! [D_435,A_436,G_437] :
      ( r1_tmap_1(D_435,'#skF_1',k3_tmap_1(A_436,'#skF_1','#skF_4',D_435,'#skF_5'),G_437)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_437)
      | ~ m1_pre_topc(D_435,'#skF_4')
      | ~ m1_subset_1(G_437,u1_struct_0(D_435))
      | ~ m1_subset_1(G_437,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_435,A_436)
      | v2_struct_0(D_435)
      | ~ m1_pre_topc('#skF_4',A_436)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_36,c_213])).

tff(c_159,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_159])).

tff(c_162,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_218,plain,
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
    inference(resolution,[status(thm)],[c_215,c_162])).

tff(c_221,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_34,c_38,c_20,c_64,c_22,c_157,c_218])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.34  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.34  
% 2.65/1.34  %Foreground sorts:
% 2.65/1.34  
% 2.65/1.34  
% 2.65/1.34  %Background operators:
% 2.65/1.34  
% 2.65/1.34  
% 2.65/1.34  %Foreground operators:
% 2.65/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.65/1.34  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.34  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.65/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.34  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.65/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.65/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.34  
% 2.65/1.36  tff(f_214, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 2.65/1.36  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.65/1.36  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 2.65/1.36  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 2.65/1.36  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 2.65/1.36  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 2.65/1.36  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_20, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_16, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_18, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.65/1.36  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_60, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_62, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 2.65/1.36  tff(c_89, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 2.65/1.36  tff(c_54, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_63, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_54])).
% 2.65/1.36  tff(c_91, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_63])).
% 2.65/1.36  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_26, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 2.65/1.36  tff(c_69, plain, (![B_388, A_389]: (l1_pre_topc(B_388) | ~m1_pre_topc(B_388, A_389) | ~l1_pre_topc(A_389))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.36  tff(c_72, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_69])).
% 2.65/1.36  tff(c_81, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72])).
% 2.65/1.36  tff(c_8, plain, (![B_13, A_11]: (r1_tarski(u1_struct_0(B_13), u1_struct_0(A_11)) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.36  tff(c_92, plain, (![B_392, C_393, A_394]: (v1_tsep_1(B_392, C_393) | ~r1_tarski(u1_struct_0(B_392), u1_struct_0(C_393)) | ~m1_pre_topc(C_393, A_394) | v2_struct_0(C_393) | ~m1_pre_topc(B_392, A_394) | ~v1_tsep_1(B_392, A_394) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.65/1.36  tff(c_100, plain, (![B_398, A_399, A_400]: (v1_tsep_1(B_398, A_399) | ~m1_pre_topc(A_399, A_400) | v2_struct_0(A_399) | ~m1_pre_topc(B_398, A_400) | ~v1_tsep_1(B_398, A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | ~m1_pre_topc(B_398, A_399) | ~l1_pre_topc(A_399))), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.65/1.36  tff(c_102, plain, (![B_398]: (v1_tsep_1(B_398, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_398, '#skF_2') | ~v1_tsep_1(B_398, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_398, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_100])).
% 2.65/1.36  tff(c_109, plain, (![B_398]: (v1_tsep_1(B_398, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_398, '#skF_2') | ~v1_tsep_1(B_398, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_398, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_44, c_42, c_102])).
% 2.65/1.36  tff(c_119, plain, (![B_401]: (v1_tsep_1(B_401, '#skF_4') | ~m1_pre_topc(B_401, '#skF_2') | ~v1_tsep_1(B_401, '#skF_2') | ~m1_pre_topc(B_401, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_109])).
% 2.65/1.36  tff(c_122, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_119])).
% 2.65/1.36  tff(c_125, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_38, c_122])).
% 2.65/1.36  tff(c_143, plain, (![C_412, A_416, D_413, B_417, E_415, G_414]: (r1_tmap_1(D_413, B_417, E_415, G_414) | ~r1_tmap_1(C_412, B_417, k3_tmap_1(A_416, B_417, D_413, C_412, E_415), G_414) | ~m1_subset_1(G_414, u1_struct_0(C_412)) | ~m1_subset_1(G_414, u1_struct_0(D_413)) | ~m1_pre_topc(C_412, D_413) | ~v1_tsep_1(C_412, D_413) | ~m1_subset_1(E_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_413), u1_struct_0(B_417)))) | ~v1_funct_2(E_415, u1_struct_0(D_413), u1_struct_0(B_417)) | ~v1_funct_1(E_415) | ~m1_pre_topc(D_413, A_416) | v2_struct_0(D_413) | ~m1_pre_topc(C_412, A_416) | v2_struct_0(C_412) | ~l1_pre_topc(B_417) | ~v2_pre_topc(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(cnfTransformation, [status(thm)], [f_161])).
% 2.65/1.36  tff(c_147, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_89, c_143])).
% 2.65/1.36  tff(c_154, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_50, c_48, c_38, c_34, c_32, c_30, c_28, c_125, c_22, c_20, c_64, c_147])).
% 2.65/1.36  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_40, c_36, c_91, c_154])).
% 2.65/1.36  tff(c_157, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 2.65/1.36  tff(c_208, plain, (![D_431, E_430, B_429, G_432, A_434, C_433]: (r1_tmap_1(D_431, B_429, k3_tmap_1(A_434, B_429, C_433, D_431, E_430), G_432) | ~r1_tmap_1(C_433, B_429, E_430, G_432) | ~m1_pre_topc(D_431, C_433) | ~m1_subset_1(G_432, u1_struct_0(D_431)) | ~m1_subset_1(G_432, u1_struct_0(C_433)) | ~m1_subset_1(E_430, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_433), u1_struct_0(B_429)))) | ~v1_funct_2(E_430, u1_struct_0(C_433), u1_struct_0(B_429)) | ~v1_funct_1(E_430) | ~m1_pre_topc(D_431, A_434) | v2_struct_0(D_431) | ~m1_pre_topc(C_433, A_434) | v2_struct_0(C_433) | ~l1_pre_topc(B_429) | ~v2_pre_topc(B_429) | v2_struct_0(B_429) | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.65/1.36  tff(c_210, plain, (![D_431, A_434, G_432]: (r1_tmap_1(D_431, '#skF_1', k3_tmap_1(A_434, '#skF_1', '#skF_4', D_431, '#skF_5'), G_432) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_432) | ~m1_pre_topc(D_431, '#skF_4') | ~m1_subset_1(G_432, u1_struct_0(D_431)) | ~m1_subset_1(G_432, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_431, A_434) | v2_struct_0(D_431) | ~m1_pre_topc('#skF_4', A_434) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(resolution, [status(thm)], [c_28, c_208])).
% 2.65/1.36  tff(c_213, plain, (![D_431, A_434, G_432]: (r1_tmap_1(D_431, '#skF_1', k3_tmap_1(A_434, '#skF_1', '#skF_4', D_431, '#skF_5'), G_432) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_432) | ~m1_pre_topc(D_431, '#skF_4') | ~m1_subset_1(G_432, u1_struct_0(D_431)) | ~m1_subset_1(G_432, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_431, A_434) | v2_struct_0(D_431) | ~m1_pre_topc('#skF_4', A_434) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_434) | ~v2_pre_topc(A_434) | v2_struct_0(A_434))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_32, c_30, c_210])).
% 2.65/1.36  tff(c_215, plain, (![D_435, A_436, G_437]: (r1_tmap_1(D_435, '#skF_1', k3_tmap_1(A_436, '#skF_1', '#skF_4', D_435, '#skF_5'), G_437) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_437) | ~m1_pre_topc(D_435, '#skF_4') | ~m1_subset_1(G_437, u1_struct_0(D_435)) | ~m1_subset_1(G_437, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_435, A_436) | v2_struct_0(D_435) | ~m1_pre_topc('#skF_4', A_436) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(negUnitSimplification, [status(thm)], [c_52, c_36, c_213])).
% 2.65/1.36  tff(c_159, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_63])).
% 2.65/1.36  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_159])).
% 2.65/1.36  tff(c_162, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_63])).
% 2.65/1.36  tff(c_218, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_215, c_162])).
% 2.65/1.36  tff(c_221, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_34, c_38, c_20, c_64, c_22, c_157, c_218])).
% 2.65/1.36  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_221])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 24
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 6
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 2
% 2.65/1.36  #Demod        : 67
% 2.65/1.36  #Tautology    : 10
% 2.65/1.36  #SimpNegUnit  : 11
% 2.65/1.36  #BackRed      : 0
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.37  Preprocessing        : 0.37
% 2.65/1.37  Parsing              : 0.18
% 2.65/1.37  CNF conversion       : 0.06
% 2.65/1.37  Main loop            : 0.23
% 2.65/1.37  Inferencing          : 0.08
% 2.65/1.37  Reduction            : 0.07
% 2.65/1.37  Demodulation         : 0.06
% 2.65/1.37  BG Simplification    : 0.02
% 2.65/1.37  Subsumption          : 0.04
% 2.65/1.37  Abstraction          : 0.01
% 2.65/1.37  MUC search           : 0.00
% 2.65/1.37  Cooper               : 0.00
% 2.65/1.37  Total                : 0.63
% 2.65/1.37  Index Insertion      : 0.00
% 2.65/1.37  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
