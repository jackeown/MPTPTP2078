%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:18 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 565 expanded)
%              Number of leaves         :   36 ( 227 expanded)
%              Depth                    :   14
%              Number of atoms          :  561 (5040 expanded)
%              Number of equality atoms :   46 ( 279 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_174,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_112,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_42,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_40,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_381,plain,(
    ! [A_258,B_259,D_260] :
      ( r2_funct_2(A_258,B_259,D_260,D_260)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(D_260,A_258,B_259)
      | ~ v1_funct_1(D_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_387,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_381])).

tff(c_396,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_387])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_30,plain,(
    '#skF_5' = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_79,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_50])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_36,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_34,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_81,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_658,plain,(
    ! [C_322,D_325,B_324,E_321,A_323] :
      ( v1_funct_2(k3_tmap_1(A_323,B_324,C_322,D_325,E_321),u1_struct_0(D_325),u1_struct_0(B_324))
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_322),u1_struct_0(B_324))
      | ~ v1_funct_1(E_321)
      | ~ m1_pre_topc(D_325,A_323)
      | ~ m1_pre_topc(C_322,A_323)
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_662,plain,(
    ! [A_323,D_325] :
      ( v1_funct_2(k3_tmap_1(A_323,'#skF_3','#skF_2',D_325,'#skF_8'),u1_struct_0(D_325),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_325,A_323)
      | ~ m1_pre_topc('#skF_2',A_323)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_82,c_658])).

tff(c_671,plain,(
    ! [A_323,D_325] :
      ( v1_funct_2(k3_tmap_1(A_323,'#skF_3','#skF_2',D_325,'#skF_8'),u1_struct_0(D_325),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_325,A_323)
      | ~ m1_pre_topc('#skF_2',A_323)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_662])).

tff(c_677,plain,(
    ! [A_326,D_327] :
      ( v1_funct_2(k3_tmap_1(A_326,'#skF_3','#skF_2',D_327,'#skF_8'),u1_struct_0(D_327),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_327,A_326)
      | ~ m1_pre_topc('#skF_2',A_326)
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_671])).

tff(c_581,plain,(
    ! [C_312,D_315,B_314,A_313,E_311] :
      ( m1_subset_1(k3_tmap_1(A_313,B_314,C_312,D_315,E_311),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_315),u1_struct_0(B_314))))
      | ~ m1_subset_1(E_311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_312),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_311,u1_struct_0(C_312),u1_struct_0(B_314))
      | ~ v1_funct_1(E_311)
      | ~ m1_pre_topc(D_315,A_313)
      | ~ m1_pre_topc(C_312,A_313)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_509,plain,(
    ! [A_290,C_289,B_291,E_288,D_292] :
      ( v1_funct_1(k3_tmap_1(A_290,B_291,C_289,D_292,E_288))
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_289),u1_struct_0(B_291))))
      | ~ v1_funct_2(E_288,u1_struct_0(C_289),u1_struct_0(B_291))
      | ~ v1_funct_1(E_288)
      | ~ m1_pre_topc(D_292,A_290)
      | ~ m1_pre_topc(C_289,A_290)
      | ~ l1_pre_topc(B_291)
      | ~ v2_pre_topc(B_291)
      | v2_struct_0(B_291)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_511,plain,(
    ! [A_290,D_292] :
      ( v1_funct_1(k3_tmap_1(A_290,'#skF_3','#skF_2',D_292,'#skF_8'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_292,A_290)
      | ~ m1_pre_topc('#skF_2',A_290)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_82,c_509])).

tff(c_516,plain,(
    ! [A_290,D_292] :
      ( v1_funct_1(k3_tmap_1(A_290,'#skF_3','#skF_2',D_292,'#skF_8'))
      | ~ m1_pre_topc(D_292,A_290)
      | ~ m1_pre_topc('#skF_2',A_290)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_511])).

tff(c_517,plain,(
    ! [A_290,D_292] :
      ( v1_funct_1(k3_tmap_1(A_290,'#skF_3','#skF_2',D_292,'#skF_8'))
      | ~ m1_pre_topc(D_292,A_290)
      | ~ m1_pre_topc('#skF_2',A_290)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_516])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_46,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_154,plain,(
    ! [B_200,F_203,C_204,D_202,A_201] :
      ( r1_funct_2(A_201,B_200,C_204,D_202,F_203,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_204,D_202)))
      | ~ v1_funct_2(F_203,C_204,D_202)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2(F_203,A_201,B_200)
      | ~ v1_funct_1(F_203)
      | v1_xboole_0(D_202)
      | v1_xboole_0(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_158,plain,(
    ! [A_201,B_200] :
      ( r1_funct_2(A_201,B_200,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2('#skF_6',A_201,B_200)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_200) ) ),
    inference(resolution,[status(thm)],[c_44,c_154])).

tff(c_166,plain,(
    ! [A_201,B_200] :
      ( r1_funct_2(A_201,B_200,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2('#skF_6',A_201,B_200)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_158])).

tff(c_170,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_105,plain,(
    ! [A_191] :
      ( m1_subset_1('#skF_1'(A_191),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_191] :
      ( v1_xboole_0('#skF_1'(A_191))
      | ~ v1_xboole_0(u1_struct_0(A_191))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_173,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_109])).

tff(c_176,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_173])).

tff(c_177,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_176])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_1'(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_10])).

tff(c_183,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_180])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_183])).

tff(c_187,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_28,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_83,plain,(
    r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_191,plain,(
    ! [B_209,D_212,F_213,E_210,C_214,A_211] :
      ( F_213 = E_210
      | ~ r1_funct_2(A_211,B_209,C_214,D_212,E_210,F_213)
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_214,D_212)))
      | ~ v1_funct_2(F_213,C_214,D_212)
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_211,B_209)))
      | ~ v1_funct_2(E_210,A_211,B_209)
      | ~ v1_funct_1(E_210)
      | v1_xboole_0(D_212)
      | v1_xboole_0(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_197,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_191])).

tff(c_210,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_81,c_82,c_197])).

tff(c_211,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_210])).

tff(c_76,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_78,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_76])).

tff(c_110,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_214,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_110])).

tff(c_324,plain,(
    ! [B_252,E_251,D_254,C_250,A_253] :
      ( k3_tmap_1(A_253,B_252,C_250,D_254,E_251) = k2_partfun1(u1_struct_0(C_250),u1_struct_0(B_252),E_251,u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,C_250)
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_250),u1_struct_0(B_252))))
      | ~ v1_funct_2(E_251,u1_struct_0(C_250),u1_struct_0(B_252))
      | ~ v1_funct_1(E_251)
      | ~ m1_pre_topc(D_254,A_253)
      | ~ m1_pre_topc(C_250,A_253)
      | ~ l1_pre_topc(B_252)
      | ~ v2_pre_topc(B_252)
      | v2_struct_0(B_252)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_328,plain,(
    ! [A_253,D_254] :
      ( k3_tmap_1(A_253,'#skF_3','#skF_2',D_254,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_254,A_253)
      | ~ m1_pre_topc('#skF_2',A_253)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_82,c_324])).

tff(c_334,plain,(
    ! [A_253,D_254] :
      ( k3_tmap_1(A_253,'#skF_3','#skF_2',D_254,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_254))
      | ~ m1_pre_topc(D_254,'#skF_2')
      | ~ m1_pre_topc(D_254,A_253)
      | ~ m1_pre_topc('#skF_2',A_253)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_328])).

tff(c_340,plain,(
    ! [A_255,D_256] :
      ( k3_tmap_1(A_255,'#skF_3','#skF_2',D_256,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_256))
      | ~ m1_pre_topc(D_256,'#skF_2')
      | ~ m1_pre_topc(D_256,A_255)
      | ~ m1_pre_topc('#skF_2',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_334])).

tff(c_342,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_340])).

tff(c_347,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_342])).

tff(c_348,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_347])).

tff(c_264,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k2_partfun1(u1_struct_0(A_224),u1_struct_0(B_225),C_226,u1_struct_0(D_227)) = k2_tmap_1(A_224,B_225,C_226,D_227)
      | ~ m1_pre_topc(D_227,A_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_224),u1_struct_0(B_225))))
      | ~ v1_funct_2(C_226,u1_struct_0(A_224),u1_struct_0(B_225))
      | ~ v1_funct_1(C_226)
      | ~ l1_pre_topc(B_225)
      | ~ v2_pre_topc(B_225)
      | v2_struct_0(B_225)
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_266,plain,(
    ! [D_227] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_227)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_227)
      | ~ m1_pre_topc(D_227,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_82,c_264])).

tff(c_271,plain,(
    ! [D_227] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_227)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_227)
      | ~ m1_pre_topc(D_227,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_36,c_81,c_266])).

tff(c_272,plain,(
    ! [D_227] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_227)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_227)
      | ~ m1_pre_topc(D_227,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_271])).

tff(c_356,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_272])).

tff(c_363,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_356])).

tff(c_70,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_80,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7')
    | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70])).

tff(c_129,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_80])).

tff(c_368,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_129])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_368])).

tff(c_372,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_397,plain,(
    ! [D_261,C_262,A_263,B_264] :
      ( D_261 = C_262
      | ~ r2_funct_2(A_263,B_264,C_262,D_261)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ v1_funct_2(D_261,A_263,B_264)
      | ~ v1_funct_1(D_261)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ v1_funct_2(C_262,A_263,B_264)
      | ~ v1_funct_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_405,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_372,c_397])).

tff(c_420,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = '#skF_7'
    | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_405])).

tff(c_531,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_534,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_517,c_531])).

tff(c_537,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_534])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_537])).

tff(c_540,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_542,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_588,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_581,c_542])).

tff(c_602,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_79,c_54,c_36,c_81,c_82,c_588])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_602])).

tff(c_605,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_628,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_605])).

tff(c_680,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_677,c_628])).

tff(c_683,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_680])).

tff(c_685,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_683])).

tff(c_686,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_605])).

tff(c_779,plain,(
    ! [A_350,B_349,D_351,E_348,C_347] :
      ( k3_tmap_1(A_350,B_349,C_347,D_351,E_348) = k2_partfun1(u1_struct_0(C_347),u1_struct_0(B_349),E_348,u1_struct_0(D_351))
      | ~ m1_pre_topc(D_351,C_347)
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_347),u1_struct_0(B_349))))
      | ~ v1_funct_2(E_348,u1_struct_0(C_347),u1_struct_0(B_349))
      | ~ v1_funct_1(E_348)
      | ~ m1_pre_topc(D_351,A_350)
      | ~ m1_pre_topc(C_347,A_350)
      | ~ l1_pre_topc(B_349)
      | ~ v2_pre_topc(B_349)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_783,plain,(
    ! [A_350,D_351] :
      ( k3_tmap_1(A_350,'#skF_3','#skF_2',D_351,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_351))
      | ~ m1_pre_topc(D_351,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_pre_topc(D_351,A_350)
      | ~ m1_pre_topc('#skF_2',A_350)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(resolution,[status(thm)],[c_82,c_779])).

tff(c_789,plain,(
    ! [A_350,D_351] :
      ( k3_tmap_1(A_350,'#skF_3','#skF_2',D_351,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_351))
      | ~ m1_pre_topc(D_351,'#skF_2')
      | ~ m1_pre_topc(D_351,A_350)
      | ~ m1_pre_topc('#skF_2',A_350)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_36,c_81,c_783])).

tff(c_795,plain,(
    ! [A_352,D_353] :
      ( k3_tmap_1(A_352,'#skF_3','#skF_2',D_353,'#skF_8') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_353))
      | ~ m1_pre_topc(D_353,'#skF_2')
      | ~ m1_pre_topc(D_353,A_352)
      | ~ m1_pre_topc('#skF_2',A_352)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_789])).

tff(c_797,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_795])).

tff(c_802,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = '#skF_7'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_79,c_54,c_686,c_797])).

tff(c_803,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0('#skF_4')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_802])).

tff(c_705,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k2_partfun1(u1_struct_0(A_328),u1_struct_0(B_329),C_330,u1_struct_0(D_331)) = k2_tmap_1(A_328,B_329,C_330,D_331)
      | ~ m1_pre_topc(D_331,A_328)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328),u1_struct_0(B_329))))
      | ~ v1_funct_2(C_330,u1_struct_0(A_328),u1_struct_0(B_329))
      | ~ v1_funct_1(C_330)
      | ~ l1_pre_topc(B_329)
      | ~ v2_pre_topc(B_329)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328)
      | v2_struct_0(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_707,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_331)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_331)
      | ~ m1_pre_topc(D_331,'#skF_2')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_82,c_705])).

tff(c_712,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_331)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_331)
      | ~ m1_pre_topc(D_331,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_36,c_81,c_707])).

tff(c_713,plain,(
    ! [D_331] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8',u1_struct_0(D_331)) = k2_tmap_1('#skF_2','#skF_3','#skF_8',D_331)
      | ~ m1_pre_topc(D_331,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_712])).

tff(c_811,plain,
    ( k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') = '#skF_7'
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_713])).

tff(c_818,plain,(
    k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_811])).

tff(c_421,plain,(
    ! [D_267,A_266,F_268,C_269,B_265] :
      ( r1_funct_2(A_266,B_265,C_269,D_267,F_268,F_268)
      | ~ m1_subset_1(F_268,k1_zfmisc_1(k2_zfmisc_1(C_269,D_267)))
      | ~ v1_funct_2(F_268,C_269,D_267)
      | ~ m1_subset_1(F_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_265)))
      | ~ v1_funct_2(F_268,A_266,B_265)
      | ~ v1_funct_1(F_268)
      | v1_xboole_0(D_267)
      | v1_xboole_0(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_423,plain,(
    ! [A_266,B_265] :
      ( r1_funct_2(A_266,B_265,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8','#skF_8')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_266,B_265)))
      | ~ v1_funct_2('#skF_8',A_266,B_265)
      | ~ v1_funct_1('#skF_8')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_265) ) ),
    inference(resolution,[status(thm)],[c_82,c_421])).

tff(c_430,plain,(
    ! [A_266,B_265] :
      ( r1_funct_2(A_266,B_265,u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_8','#skF_8')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(A_266,B_265)))
      | ~ v1_funct_2('#skF_8',A_266,B_265)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_81,c_423])).

tff(c_437,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_446,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_437,c_109])).

tff(c_449,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_446])).

tff(c_450,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_449])).

tff(c_453,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_10])).

tff(c_456,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_456])).

tff(c_460,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_466,plain,(
    ! [D_285,F_286,A_284,E_283,C_287,B_282] :
      ( F_286 = E_283
      | ~ r1_funct_2(A_284,B_282,C_287,D_285,E_283,F_286)
      | ~ m1_subset_1(F_286,k1_zfmisc_1(k2_zfmisc_1(C_287,D_285)))
      | ~ v1_funct_2(F_286,C_287,D_285)
      | ~ v1_funct_1(F_286)
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_282)))
      | ~ v1_funct_2(E_283,A_284,B_282)
      | ~ v1_funct_1(E_283)
      | v1_xboole_0(D_285)
      | v1_xboole_0(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_474,plain,
    ( '#skF_6' = '#skF_8'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_466])).

tff(c_492,plain,
    ( '#skF_6' = '#skF_8'
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_36,c_81,c_82,c_474])).

tff(c_493,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_460,c_492])).

tff(c_373,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_496,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_8','#skF_4'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_373])).

tff(c_822,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_496])).

tff(c_825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.56  
% 3.61/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.56  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v4_pre_topc > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.61/1.56  
% 3.61/1.56  %Foreground sorts:
% 3.61/1.56  
% 3.61/1.56  
% 3.61/1.56  %Background operators:
% 3.61/1.56  
% 3.61/1.56  
% 3.61/1.56  %Foreground operators:
% 3.61/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.61/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.56  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.61/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.56  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.61/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.61/1.56  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.61/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.61/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.56  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.61/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.56  
% 3.61/1.59  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 3.61/1.59  tff(f_48, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.61/1.59  tff(f_174, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.61/1.59  tff(f_85, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.61/1.59  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.61/1.59  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.61/1.59  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.61/1.59  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.61/1.59  tff(c_42, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_40, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_381, plain, (![A_258, B_259, D_260]: (r2_funct_2(A_258, B_259, D_260, D_260) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(D_260, A_258, B_259) | ~v1_funct_1(D_260))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.59  tff(c_387, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_38, c_381])).
% 3.61/1.59  tff(c_396, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_387])).
% 3.61/1.59  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_30, plain, ('#skF_5'='#skF_2'), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_79, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_50])).
% 3.61/1.59  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_36, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_34, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_81, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 3.61/1.59  tff(c_32, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_82, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.61/1.59  tff(c_658, plain, (![C_322, D_325, B_324, E_321, A_323]: (v1_funct_2(k3_tmap_1(A_323, B_324, C_322, D_325, E_321), u1_struct_0(D_325), u1_struct_0(B_324)) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_322), u1_struct_0(B_324)))) | ~v1_funct_2(E_321, u1_struct_0(C_322), u1_struct_0(B_324)) | ~v1_funct_1(E_321) | ~m1_pre_topc(D_325, A_323) | ~m1_pre_topc(C_322, A_323) | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.61/1.59  tff(c_662, plain, (![A_323, D_325]: (v1_funct_2(k3_tmap_1(A_323, '#skF_3', '#skF_2', D_325, '#skF_8'), u1_struct_0(D_325), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_325, A_323) | ~m1_pre_topc('#skF_2', A_323) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(resolution, [status(thm)], [c_82, c_658])).
% 3.61/1.59  tff(c_671, plain, (![A_323, D_325]: (v1_funct_2(k3_tmap_1(A_323, '#skF_3', '#skF_2', D_325, '#skF_8'), u1_struct_0(D_325), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_325, A_323) | ~m1_pre_topc('#skF_2', A_323) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_662])).
% 3.61/1.59  tff(c_677, plain, (![A_326, D_327]: (v1_funct_2(k3_tmap_1(A_326, '#skF_3', '#skF_2', D_327, '#skF_8'), u1_struct_0(D_327), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_327, A_326) | ~m1_pre_topc('#skF_2', A_326) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(negUnitSimplification, [status(thm)], [c_62, c_671])).
% 3.61/1.59  tff(c_581, plain, (![C_312, D_315, B_314, A_313, E_311]: (m1_subset_1(k3_tmap_1(A_313, B_314, C_312, D_315, E_311), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_315), u1_struct_0(B_314)))) | ~m1_subset_1(E_311, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_312), u1_struct_0(B_314)))) | ~v1_funct_2(E_311, u1_struct_0(C_312), u1_struct_0(B_314)) | ~v1_funct_1(E_311) | ~m1_pre_topc(D_315, A_313) | ~m1_pre_topc(C_312, A_313) | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.61/1.59  tff(c_509, plain, (![A_290, C_289, B_291, E_288, D_292]: (v1_funct_1(k3_tmap_1(A_290, B_291, C_289, D_292, E_288)) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_289), u1_struct_0(B_291)))) | ~v1_funct_2(E_288, u1_struct_0(C_289), u1_struct_0(B_291)) | ~v1_funct_1(E_288) | ~m1_pre_topc(D_292, A_290) | ~m1_pre_topc(C_289, A_290) | ~l1_pre_topc(B_291) | ~v2_pre_topc(B_291) | v2_struct_0(B_291) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.61/1.59  tff(c_511, plain, (![A_290, D_292]: (v1_funct_1(k3_tmap_1(A_290, '#skF_3', '#skF_2', D_292, '#skF_8')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_292, A_290) | ~m1_pre_topc('#skF_2', A_290) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(resolution, [status(thm)], [c_82, c_509])).
% 3.61/1.59  tff(c_516, plain, (![A_290, D_292]: (v1_funct_1(k3_tmap_1(A_290, '#skF_3', '#skF_2', D_292, '#skF_8')) | ~m1_pre_topc(D_292, A_290) | ~m1_pre_topc('#skF_2', A_290) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_511])).
% 3.61/1.59  tff(c_517, plain, (![A_290, D_292]: (v1_funct_1(k3_tmap_1(A_290, '#skF_3', '#skF_2', D_292, '#skF_8')) | ~m1_pre_topc(D_292, A_290) | ~m1_pre_topc('#skF_2', A_290) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(negUnitSimplification, [status(thm)], [c_62, c_516])).
% 3.61/1.59  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_46, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_154, plain, (![B_200, F_203, C_204, D_202, A_201]: (r1_funct_2(A_201, B_200, C_204, D_202, F_203, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_204, D_202))) | ~v1_funct_2(F_203, C_204, D_202) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2(F_203, A_201, B_200) | ~v1_funct_1(F_203) | v1_xboole_0(D_202) | v1_xboole_0(B_200))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.59  tff(c_158, plain, (![A_201, B_200]: (r1_funct_2(A_201, B_200, u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2('#skF_6', A_201, B_200) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_200))), inference(resolution, [status(thm)], [c_44, c_154])).
% 3.61/1.59  tff(c_166, plain, (![A_201, B_200]: (r1_funct_2(A_201, B_200, u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2('#skF_6', A_201, B_200) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_200))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_158])).
% 3.61/1.59  tff(c_170, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_166])).
% 3.61/1.59  tff(c_105, plain, (![A_191]: (m1_subset_1('#skF_1'(A_191), k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.61/1.59  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.59  tff(c_109, plain, (![A_191]: (v1_xboole_0('#skF_1'(A_191)) | ~v1_xboole_0(u1_struct_0(A_191)) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_105, c_2])).
% 3.61/1.59  tff(c_173, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_170, c_109])).
% 3.61/1.59  tff(c_176, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_173])).
% 3.61/1.59  tff(c_177, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_176])).
% 3.61/1.59  tff(c_10, plain, (![A_8]: (~v1_xboole_0('#skF_1'(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.61/1.59  tff(c_180, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_177, c_10])).
% 3.61/1.59  tff(c_183, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_180])).
% 3.61/1.59  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_183])).
% 3.61/1.59  tff(c_187, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_166])).
% 3.61/1.59  tff(c_28, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_83, plain, (r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 3.61/1.59  tff(c_191, plain, (![B_209, D_212, F_213, E_210, C_214, A_211]: (F_213=E_210 | ~r1_funct_2(A_211, B_209, C_214, D_212, E_210, F_213) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_214, D_212))) | ~v1_funct_2(F_213, C_214, D_212) | ~v1_funct_1(F_213) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_211, B_209))) | ~v1_funct_2(E_210, A_211, B_209) | ~v1_funct_1(E_210) | v1_xboole_0(D_212) | v1_xboole_0(B_209))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.59  tff(c_197, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_191])).
% 3.61/1.59  tff(c_210, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_81, c_82, c_197])).
% 3.61/1.59  tff(c_211, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_187, c_210])).
% 3.61/1.59  tff(c_76, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_78, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_76])).
% 3.61/1.59  tff(c_110, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitLeft, [status(thm)], [c_78])).
% 3.61/1.59  tff(c_214, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_110])).
% 3.61/1.59  tff(c_324, plain, (![B_252, E_251, D_254, C_250, A_253]: (k3_tmap_1(A_253, B_252, C_250, D_254, E_251)=k2_partfun1(u1_struct_0(C_250), u1_struct_0(B_252), E_251, u1_struct_0(D_254)) | ~m1_pre_topc(D_254, C_250) | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_250), u1_struct_0(B_252)))) | ~v1_funct_2(E_251, u1_struct_0(C_250), u1_struct_0(B_252)) | ~v1_funct_1(E_251) | ~m1_pre_topc(D_254, A_253) | ~m1_pre_topc(C_250, A_253) | ~l1_pre_topc(B_252) | ~v2_pre_topc(B_252) | v2_struct_0(B_252) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.61/1.59  tff(c_328, plain, (![A_253, D_254]: (k3_tmap_1(A_253, '#skF_3', '#skF_2', D_254, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_254)) | ~m1_pre_topc(D_254, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_254, A_253) | ~m1_pre_topc('#skF_2', A_253) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_82, c_324])).
% 3.61/1.59  tff(c_334, plain, (![A_253, D_254]: (k3_tmap_1(A_253, '#skF_3', '#skF_2', D_254, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_254)) | ~m1_pre_topc(D_254, '#skF_2') | ~m1_pre_topc(D_254, A_253) | ~m1_pre_topc('#skF_2', A_253) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_328])).
% 3.61/1.59  tff(c_340, plain, (![A_255, D_256]: (k3_tmap_1(A_255, '#skF_3', '#skF_2', D_256, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_256)) | ~m1_pre_topc(D_256, '#skF_2') | ~m1_pre_topc(D_256, A_255) | ~m1_pre_topc('#skF_2', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(negUnitSimplification, [status(thm)], [c_62, c_334])).
% 3.61/1.59  tff(c_342, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_340])).
% 3.61/1.59  tff(c_347, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_342])).
% 3.61/1.59  tff(c_348, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_347])).
% 3.61/1.59  tff(c_264, plain, (![A_224, B_225, C_226, D_227]: (k2_partfun1(u1_struct_0(A_224), u1_struct_0(B_225), C_226, u1_struct_0(D_227))=k2_tmap_1(A_224, B_225, C_226, D_227) | ~m1_pre_topc(D_227, A_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_224), u1_struct_0(B_225)))) | ~v1_funct_2(C_226, u1_struct_0(A_224), u1_struct_0(B_225)) | ~v1_funct_1(C_226) | ~l1_pre_topc(B_225) | ~v2_pre_topc(B_225) | v2_struct_0(B_225) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.61/1.59  tff(c_266, plain, (![D_227]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_227))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_227) | ~m1_pre_topc(D_227, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_264])).
% 3.61/1.59  tff(c_271, plain, (![D_227]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_227))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_227) | ~m1_pre_topc(D_227, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_36, c_81, c_266])).
% 3.61/1.59  tff(c_272, plain, (![D_227]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_227))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_227) | ~m1_pre_topc(D_227, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_271])).
% 3.61/1.59  tff(c_356, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_348, c_272])).
% 3.61/1.59  tff(c_363, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_356])).
% 3.61/1.59  tff(c_70, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 3.61/1.59  tff(c_80, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7') | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70])).
% 3.61/1.59  tff(c_129, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_80])).
% 3.61/1.59  tff(c_368, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_129])).
% 3.61/1.59  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_368])).
% 3.61/1.59  tff(c_372, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.61/1.59  tff(c_397, plain, (![D_261, C_262, A_263, B_264]: (D_261=C_262 | ~r2_funct_2(A_263, B_264, C_262, D_261) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~v1_funct_2(D_261, A_263, B_264) | ~v1_funct_1(D_261) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~v1_funct_2(C_262, A_263, B_264) | ~v1_funct_1(C_262))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.59  tff(c_405, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_372, c_397])).
% 3.61/1.59  tff(c_420, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')='#skF_7' | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_405])).
% 3.61/1.59  tff(c_531, plain, (~v1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'))), inference(splitLeft, [status(thm)], [c_420])).
% 3.61/1.59  tff(c_534, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_517, c_531])).
% 3.61/1.59  tff(c_537, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_534])).
% 3.61/1.59  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_537])).
% 3.61/1.59  tff(c_540, plain, (~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_420])).
% 3.61/1.59  tff(c_542, plain, (~m1_subset_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_540])).
% 3.61/1.59  tff(c_588, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_581, c_542])).
% 3.61/1.59  tff(c_602, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_79, c_54, c_36, c_81, c_82, c_588])).
% 3.61/1.59  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_602])).
% 3.61/1.59  tff(c_605, plain, (~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_540])).
% 3.61/1.59  tff(c_628, plain, (~v1_funct_2(k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_605])).
% 3.61/1.59  tff(c_680, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_677, c_628])).
% 3.61/1.59  tff(c_683, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_680])).
% 3.61/1.59  tff(c_685, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_683])).
% 3.61/1.59  tff(c_686, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_605])).
% 3.61/1.59  tff(c_779, plain, (![A_350, B_349, D_351, E_348, C_347]: (k3_tmap_1(A_350, B_349, C_347, D_351, E_348)=k2_partfun1(u1_struct_0(C_347), u1_struct_0(B_349), E_348, u1_struct_0(D_351)) | ~m1_pre_topc(D_351, C_347) | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_347), u1_struct_0(B_349)))) | ~v1_funct_2(E_348, u1_struct_0(C_347), u1_struct_0(B_349)) | ~v1_funct_1(E_348) | ~m1_pre_topc(D_351, A_350) | ~m1_pre_topc(C_347, A_350) | ~l1_pre_topc(B_349) | ~v2_pre_topc(B_349) | v2_struct_0(B_349) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.61/1.59  tff(c_783, plain, (![A_350, D_351]: (k3_tmap_1(A_350, '#skF_3', '#skF_2', D_351, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_351)) | ~m1_pre_topc(D_351, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc(D_351, A_350) | ~m1_pre_topc('#skF_2', A_350) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(resolution, [status(thm)], [c_82, c_779])).
% 3.61/1.59  tff(c_789, plain, (![A_350, D_351]: (k3_tmap_1(A_350, '#skF_3', '#skF_2', D_351, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_351)) | ~m1_pre_topc(D_351, '#skF_2') | ~m1_pre_topc(D_351, A_350) | ~m1_pre_topc('#skF_2', A_350) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350) | v2_struct_0(A_350))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_36, c_81, c_783])).
% 3.61/1.59  tff(c_795, plain, (![A_352, D_353]: (k3_tmap_1(A_352, '#skF_3', '#skF_2', D_353, '#skF_8')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_353)) | ~m1_pre_topc(D_353, '#skF_2') | ~m1_pre_topc(D_353, A_352) | ~m1_pre_topc('#skF_2', A_352) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(negUnitSimplification, [status(thm)], [c_62, c_789])).
% 3.61/1.59  tff(c_797, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_795])).
% 3.61/1.59  tff(c_802, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))='#skF_7' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_79, c_54, c_686, c_797])).
% 3.61/1.59  tff(c_803, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0('#skF_4'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_68, c_802])).
% 3.61/1.59  tff(c_705, plain, (![A_328, B_329, C_330, D_331]: (k2_partfun1(u1_struct_0(A_328), u1_struct_0(B_329), C_330, u1_struct_0(D_331))=k2_tmap_1(A_328, B_329, C_330, D_331) | ~m1_pre_topc(D_331, A_328) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_328), u1_struct_0(B_329)))) | ~v1_funct_2(C_330, u1_struct_0(A_328), u1_struct_0(B_329)) | ~v1_funct_1(C_330) | ~l1_pre_topc(B_329) | ~v2_pre_topc(B_329) | v2_struct_0(B_329) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328) | v2_struct_0(A_328))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.61/1.59  tff(c_707, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_331))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_331) | ~m1_pre_topc(D_331, '#skF_2') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_705])).
% 3.61/1.59  tff(c_712, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_331))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_331) | ~m1_pre_topc(D_331, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_36, c_81, c_707])).
% 3.61/1.59  tff(c_713, plain, (![D_331]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', u1_struct_0(D_331))=k2_tmap_1('#skF_2', '#skF_3', '#skF_8', D_331) | ~m1_pre_topc(D_331, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_712])).
% 3.61/1.59  tff(c_811, plain, (k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')='#skF_7' | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_803, c_713])).
% 3.61/1.59  tff(c_818, plain, (k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_811])).
% 3.61/1.59  tff(c_421, plain, (![D_267, A_266, F_268, C_269, B_265]: (r1_funct_2(A_266, B_265, C_269, D_267, F_268, F_268) | ~m1_subset_1(F_268, k1_zfmisc_1(k2_zfmisc_1(C_269, D_267))) | ~v1_funct_2(F_268, C_269, D_267) | ~m1_subset_1(F_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))) | ~v1_funct_2(F_268, A_266, B_265) | ~v1_funct_1(F_268) | v1_xboole_0(D_267) | v1_xboole_0(B_265))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.59  tff(c_423, plain, (![A_266, B_265]: (r1_funct_2(A_266, B_265, u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', '#skF_8') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))) | ~v1_funct_2('#skF_8', A_266, B_265) | ~v1_funct_1('#skF_8') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_265))), inference(resolution, [status(thm)], [c_82, c_421])).
% 3.61/1.59  tff(c_430, plain, (![A_266, B_265]: (r1_funct_2(A_266, B_265, u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))) | ~v1_funct_2('#skF_8', A_266, B_265) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_265))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_81, c_423])).
% 3.61/1.59  tff(c_437, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_430])).
% 3.61/1.59  tff(c_446, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_437, c_109])).
% 3.61/1.59  tff(c_449, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_446])).
% 3.61/1.59  tff(c_450, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_449])).
% 3.61/1.59  tff(c_453, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_450, c_10])).
% 3.61/1.59  tff(c_456, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_453])).
% 3.61/1.59  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_456])).
% 3.61/1.59  tff(c_460, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_430])).
% 3.61/1.59  tff(c_466, plain, (![D_285, F_286, A_284, E_283, C_287, B_282]: (F_286=E_283 | ~r1_funct_2(A_284, B_282, C_287, D_285, E_283, F_286) | ~m1_subset_1(F_286, k1_zfmisc_1(k2_zfmisc_1(C_287, D_285))) | ~v1_funct_2(F_286, C_287, D_285) | ~v1_funct_1(F_286) | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_282))) | ~v1_funct_2(E_283, A_284, B_282) | ~v1_funct_1(E_283) | v1_xboole_0(D_285) | v1_xboole_0(B_282))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.61/1.59  tff(c_474, plain, ('#skF_6'='#skF_8' | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_466])).
% 3.61/1.59  tff(c_492, plain, ('#skF_6'='#skF_8' | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_36, c_81, c_82, c_474])).
% 3.61/1.59  tff(c_493, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_460, c_492])).
% 3.61/1.59  tff(c_373, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'), '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 3.61/1.59  tff(c_496, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_8', '#skF_4'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_373])).
% 3.61/1.59  tff(c_822, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_496])).
% 3.61/1.59  tff(c_825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_396, c_822])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 0
% 3.61/1.59  #Sup     : 124
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 14
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 12
% 3.61/1.59  #Demod        : 337
% 3.61/1.59  #Tautology    : 53
% 3.61/1.59  #SimpNegUnit  : 56
% 3.61/1.59  #BackRed      : 20
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.59  #Strategies tried      : 1
% 3.61/1.59  
% 3.61/1.59  Timing (in seconds)
% 3.61/1.59  ----------------------
% 3.61/1.59  Preprocessing        : 0.38
% 3.61/1.59  Parsing              : 0.19
% 3.61/1.59  CNF conversion       : 0.05
% 3.61/1.59  Main loop            : 0.42
% 3.61/1.59  Inferencing          : 0.14
% 3.61/1.59  Reduction            : 0.15
% 3.61/1.59  Demodulation         : 0.11
% 3.61/1.59  BG Simplification    : 0.03
% 3.61/1.59  Subsumption          : 0.07
% 3.61/1.59  Abstraction          : 0.02
% 3.61/1.59  MUC search           : 0.00
% 3.61/1.59  Cooper               : 0.00
% 3.61/1.59  Total                : 0.85
% 3.61/1.59  Index Insertion      : 0.00
% 3.61/1.59  Index Deletion       : 0.00
% 3.61/1.59  Index Matching       : 0.00
% 3.61/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
