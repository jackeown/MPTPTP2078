%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:20 EST 2020

% Result     : Theorem 9.80s
% Output     : CNFRefutation 9.92s
% Verified   : 
% Statistics : Number of formulae       :  172 (7070 expanded)
%              Number of leaves         :   35 (2811 expanded)
%              Depth                    :   37
%              Number of atoms          :  869 (64743 expanded)
%              Number of equality atoms :   46 (4017 expanded)
%              Maximal formula depth    :   30 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_305,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(D,B,k2_tmap_1(A,B,E,D),F) )
                                   => r1_tmap_1(C,B,k2_tmap_1(A,B,E,C),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_132,axiom,(
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

tff(f_100,axiom,(
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

tff(f_162,axiom,(
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

tff(f_244,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_41,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_206,axiom,(
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

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_34,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_67,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_32,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_22,plain,(
    ! [A_69] :
      ( m1_pre_topc(A_69,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_418,plain,(
    ! [C_353,D_350,E_352,A_349,B_351] :
      ( k3_tmap_1(A_349,B_351,C_353,D_350,E_352) = k2_partfun1(u1_struct_0(C_353),u1_struct_0(B_351),E_352,u1_struct_0(D_350))
      | ~ m1_pre_topc(D_350,C_353)
      | ~ m1_subset_1(E_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_353),u1_struct_0(B_351))))
      | ~ v1_funct_2(E_352,u1_struct_0(C_353),u1_struct_0(B_351))
      | ~ v1_funct_1(E_352)
      | ~ m1_pre_topc(D_350,A_349)
      | ~ m1_pre_topc(C_353,A_349)
      | ~ l1_pre_topc(B_351)
      | ~ v2_pre_topc(B_351)
      | v2_struct_0(B_351)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_422,plain,(
    ! [A_349,D_350] :
      ( k3_tmap_1(A_349,'#skF_2','#skF_1',D_350,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_350))
      | ~ m1_pre_topc(D_350,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_350,A_349)
      | ~ m1_pre_topc('#skF_1',A_349)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(resolution,[status(thm)],[c_42,c_418])).

tff(c_426,plain,(
    ! [A_349,D_350] :
      ( k3_tmap_1(A_349,'#skF_2','#skF_1',D_350,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_350))
      | ~ m1_pre_topc(D_350,'#skF_1')
      | ~ m1_pre_topc(D_350,A_349)
      | ~ m1_pre_topc('#skF_1',A_349)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_44,c_422])).

tff(c_446,plain,(
    ! [A_361,D_362] :
      ( k3_tmap_1(A_361,'#skF_2','#skF_1',D_362,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_362))
      | ~ m1_pre_topc(D_362,'#skF_1')
      | ~ m1_pre_topc(D_362,A_361)
      | ~ m1_pre_topc('#skF_1',A_361)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_426])).

tff(c_454,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_446])).

tff(c_468,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_454])).

tff(c_469,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_468])).

tff(c_478,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_481,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_478])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_481])).

tff(c_487,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_486,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_381,plain,(
    ! [A_332,B_333,C_334,D_335] :
      ( k2_partfun1(u1_struct_0(A_332),u1_struct_0(B_333),C_334,u1_struct_0(D_335)) = k2_tmap_1(A_332,B_333,C_334,D_335)
      | ~ m1_pre_topc(D_335,A_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332),u1_struct_0(B_333))))
      | ~ v1_funct_2(C_334,u1_struct_0(A_332),u1_struct_0(B_333))
      | ~ v1_funct_1(C_334)
      | ~ l1_pre_topc(B_333)
      | ~ v2_pre_topc(B_333)
      | v2_struct_0(B_333)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_383,plain,(
    ! [D_335] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_335)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_335)
      | ~ m1_pre_topc(D_335,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_381])).

tff(c_386,plain,(
    ! [D_335] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_335)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_335)
      | ~ m1_pre_topc(D_335,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_46,c_44,c_383])).

tff(c_387,plain,(
    ! [D_335] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_335)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_335)
      | ~ m1_pre_topc(D_335,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_386])).

tff(c_546,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_387])).

tff(c_553,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_546])).

tff(c_305,plain,(
    ! [C_323,D_321,B_322,E_325,A_324] :
      ( v1_funct_1(k3_tmap_1(A_324,B_322,C_323,D_321,E_325))
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323),u1_struct_0(B_322))))
      | ~ v1_funct_2(E_325,u1_struct_0(C_323),u1_struct_0(B_322))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc(D_321,A_324)
      | ~ m1_pre_topc(C_323,A_324)
      | ~ l1_pre_topc(B_322)
      | ~ v2_pre_topc(B_322)
      | v2_struct_0(B_322)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_307,plain,(
    ! [A_324,D_321] :
      ( v1_funct_1(k3_tmap_1(A_324,'#skF_2','#skF_1',D_321,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_321,A_324)
      | ~ m1_pre_topc('#skF_1',A_324)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(resolution,[status(thm)],[c_42,c_305])).

tff(c_310,plain,(
    ! [A_324,D_321] :
      ( v1_funct_1(k3_tmap_1(A_324,'#skF_2','#skF_1',D_321,'#skF_5'))
      | ~ m1_pre_topc(D_321,A_324)
      | ~ m1_pre_topc('#skF_1',A_324)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_44,c_307])).

tff(c_311,plain,(
    ! [A_324,D_321] :
      ( v1_funct_1(k3_tmap_1(A_324,'#skF_2','#skF_1',D_321,'#skF_5'))
      | ~ m1_pre_topc(D_321,A_324)
      | ~ m1_pre_topc('#skF_1',A_324)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_310])).

tff(c_567,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_311])).

tff(c_577,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_487,c_48,c_567])).

tff(c_578,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_577])).

tff(c_397,plain,(
    ! [B_338,C_339,E_341,D_337,A_340] :
      ( v1_funct_2(k3_tmap_1(A_340,B_338,C_339,D_337,E_341),u1_struct_0(D_337),u1_struct_0(B_338))
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_339),u1_struct_0(B_338))))
      | ~ v1_funct_2(E_341,u1_struct_0(C_339),u1_struct_0(B_338))
      | ~ v1_funct_1(E_341)
      | ~ m1_pre_topc(D_337,A_340)
      | ~ m1_pre_topc(C_339,A_340)
      | ~ l1_pre_topc(B_338)
      | ~ v2_pre_topc(B_338)
      | v2_struct_0(B_338)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_399,plain,(
    ! [A_340,D_337] :
      ( v1_funct_2(k3_tmap_1(A_340,'#skF_2','#skF_1',D_337,'#skF_5'),u1_struct_0(D_337),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_337,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_42,c_397])).

tff(c_402,plain,(
    ! [A_340,D_337] :
      ( v1_funct_2(k3_tmap_1(A_340,'#skF_2','#skF_1',D_337,'#skF_5'),u1_struct_0(D_337),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_337,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_44,c_399])).

tff(c_403,plain,(
    ! [A_340,D_337] :
      ( v1_funct_2(k3_tmap_1(A_340,'#skF_2','#skF_1',D_337,'#skF_5'),u1_struct_0(D_337),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_337,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_402])).

tff(c_564,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_403])).

tff(c_574,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_487,c_48,c_564])).

tff(c_575,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_574])).

tff(c_405,plain,(
    ! [B_345,A_347,D_344,C_346,E_348] :
      ( m1_subset_1(k3_tmap_1(A_347,B_345,C_346,D_344,E_348),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344),u1_struct_0(B_345))))
      | ~ m1_subset_1(E_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0(B_345))))
      | ~ v1_funct_2(E_348,u1_struct_0(C_346),u1_struct_0(B_345))
      | ~ v1_funct_1(E_348)
      | ~ m1_pre_topc(D_344,A_347)
      | ~ m1_pre_topc(C_346,A_347)
      | ~ l1_pre_topc(B_345)
      | ~ v2_pre_topc(B_345)
      | v2_struct_0(B_345)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_18,plain,(
    ! [D_67,E_68,C_66,A_64,B_65] :
      ( v1_funct_2(k3_tmap_1(A_64,B_65,C_66,D_67,E_68),u1_struct_0(D_67),u1_struct_0(B_65))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66),u1_struct_0(B_65))))
      | ~ v1_funct_2(E_68,u1_struct_0(C_66),u1_struct_0(B_65))
      | ~ v1_funct_1(E_68)
      | ~ m1_pre_topc(D_67,A_64)
      | ~ m1_pre_topc(C_66,A_64)
      | ~ l1_pre_topc(B_65)
      | ~ v2_pre_topc(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_902,plain,(
    ! [B_386,C_381,D_383,A_385,D_380,E_384,A_382] :
      ( v1_funct_2(k3_tmap_1(A_385,B_386,D_383,D_380,k3_tmap_1(A_382,B_386,C_381,D_383,E_384)),u1_struct_0(D_380),u1_struct_0(B_386))
      | ~ v1_funct_2(k3_tmap_1(A_382,B_386,C_381,D_383,E_384),u1_struct_0(D_383),u1_struct_0(B_386))
      | ~ v1_funct_1(k3_tmap_1(A_382,B_386,C_381,D_383,E_384))
      | ~ m1_pre_topc(D_380,A_385)
      | ~ m1_pre_topc(D_383,A_385)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381),u1_struct_0(B_386))))
      | ~ v1_funct_2(E_384,u1_struct_0(C_381),u1_struct_0(B_386))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_383,A_382)
      | ~ m1_pre_topc(C_381,A_382)
      | ~ l1_pre_topc(B_386)
      | ~ v2_pre_topc(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(resolution,[status(thm)],[c_405,c_18])).

tff(c_913,plain,(
    ! [A_385,D_380] :
      ( v1_funct_2(k3_tmap_1(A_385,'#skF_2','#skF_4',D_380,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_380),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_380,A_385)
      | ~ m1_pre_topc('#skF_4',A_385)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_902])).

tff(c_922,plain,(
    ! [A_385,D_380] :
      ( v1_funct_2(k3_tmap_1(A_385,'#skF_2','#skF_4',D_380,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_380),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_380,A_385)
      | ~ m1_pre_topc('#skF_4',A_385)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_487,c_48,c_46,c_44,c_42,c_578,c_553,c_575,c_553,c_913])).

tff(c_923,plain,(
    ! [A_385,D_380] :
      ( v1_funct_2(k3_tmap_1(A_385,'#skF_2','#skF_4',D_380,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_380),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_380,A_385)
      | ~ m1_pre_topc('#skF_4',A_385)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_922])).

tff(c_20,plain,(
    ! [D_67,E_68,C_66,A_64,B_65] :
      ( v1_funct_1(k3_tmap_1(A_64,B_65,C_66,D_67,E_68))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66),u1_struct_0(B_65))))
      | ~ v1_funct_2(E_68,u1_struct_0(C_66),u1_struct_0(B_65))
      | ~ v1_funct_1(E_68)
      | ~ m1_pre_topc(D_67,A_64)
      | ~ m1_pre_topc(C_66,A_64)
      | ~ l1_pre_topc(B_65)
      | ~ v2_pre_topc(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_771,plain,(
    ! [D_376,A_375,B_379,D_373,A_378,E_377,C_374] :
      ( v1_funct_1(k3_tmap_1(A_378,B_379,D_376,D_373,k3_tmap_1(A_375,B_379,C_374,D_376,E_377)))
      | ~ v1_funct_2(k3_tmap_1(A_375,B_379,C_374,D_376,E_377),u1_struct_0(D_376),u1_struct_0(B_379))
      | ~ v1_funct_1(k3_tmap_1(A_375,B_379,C_374,D_376,E_377))
      | ~ m1_pre_topc(D_373,A_378)
      | ~ m1_pre_topc(D_376,A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_374),u1_struct_0(B_379))))
      | ~ v1_funct_2(E_377,u1_struct_0(C_374),u1_struct_0(B_379))
      | ~ v1_funct_1(E_377)
      | ~ m1_pre_topc(D_376,A_375)
      | ~ m1_pre_topc(C_374,A_375)
      | ~ l1_pre_topc(B_379)
      | ~ v2_pre_topc(B_379)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_405,c_20])).

tff(c_775,plain,(
    ! [A_378,D_373] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_4',D_373,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_373,A_378)
      | ~ m1_pre_topc('#skF_4',A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_771])).

tff(c_782,plain,(
    ! [A_378,D_373] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_4',D_373,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_373,A_378)
      | ~ m1_pre_topc('#skF_4',A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_487,c_48,c_46,c_44,c_42,c_578,c_553,c_575,c_553,c_775])).

tff(c_783,plain,(
    ! [A_378,D_373] :
      ( v1_funct_1(k3_tmap_1(A_378,'#skF_2','#skF_4',D_373,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_373,A_378)
      | ~ m1_pre_topc('#skF_4',A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378)
      | v2_struct_0(A_378) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_782])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_456,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_446])).

tff(c_472,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_52,c_456])).

tff(c_473,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_472])).

tff(c_789,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_473])).

tff(c_793,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_387])).

tff(c_800,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_793])).

tff(c_822,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_311])).

tff(c_841,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_487,c_52,c_822])).

tff(c_842,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_841])).

tff(c_819,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_403])).

tff(c_838,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_487,c_52,c_819])).

tff(c_839,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_838])).

tff(c_16,plain,(
    ! [D_67,E_68,C_66,A_64,B_65] :
      ( m1_subset_1(k3_tmap_1(A_64,B_65,C_66,D_67,E_68),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_67),u1_struct_0(B_65))))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66),u1_struct_0(B_65))))
      | ~ v1_funct_2(E_68,u1_struct_0(C_66),u1_struct_0(B_65))
      | ~ v1_funct_1(E_68)
      | ~ m1_pre_topc(D_67,A_64)
      | ~ m1_pre_topc(C_66,A_64)
      | ~ l1_pre_topc(B_65)
      | ~ v2_pre_topc(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_816,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_16])).

tff(c_835,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_487,c_52,c_46,c_44,c_42,c_816])).

tff(c_836,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_835])).

tff(c_561,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_16])).

tff(c_571,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_487,c_48,c_46,c_44,c_42,c_561])).

tff(c_572,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_571])).

tff(c_14,plain,(
    ! [B_49,C_57,D_61,A_33,E_63] :
      ( k3_tmap_1(A_33,B_49,C_57,D_61,E_63) = k2_partfun1(u1_struct_0(C_57),u1_struct_0(B_49),E_63,u1_struct_0(D_61))
      | ~ m1_pre_topc(D_61,C_57)
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_57),u1_struct_0(B_49))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_57),u1_struct_0(B_49))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc(D_61,A_33)
      | ~ m1_pre_topc(C_57,A_33)
      | ~ l1_pre_topc(B_49)
      | ~ v2_pre_topc(B_49)
      | v2_struct_0(B_49)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_588,plain,(
    ! [A_33,D_61] :
      ( k3_tmap_1(A_33,'#skF_2','#skF_4',D_61,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_61))
      | ~ m1_pre_topc(D_61,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_61,A_33)
      | ~ m1_pre_topc('#skF_4',A_33)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_572,c_14])).

tff(c_603,plain,(
    ! [A_33,D_61] :
      ( k3_tmap_1(A_33,'#skF_2','#skF_4',D_61,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_61))
      | ~ m1_pre_topc(D_61,'#skF_4')
      | ~ m1_pre_topc(D_61,A_33)
      | ~ m1_pre_topc('#skF_4',A_33)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_578,c_575,c_588])).

tff(c_604,plain,(
    ! [A_33,D_61] :
      ( k3_tmap_1(A_33,'#skF_2','#skF_4',D_61,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_61))
      | ~ m1_pre_topc(D_61,'#skF_4')
      | ~ m1_pre_topc(D_61,A_33)
      | ~ m1_pre_topc('#skF_4',A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_603])).

tff(c_1447,plain,(
    ! [A_444,D_445] :
      ( k3_tmap_1(A_444,'#skF_2','#skF_4',D_445,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_445))
      | ~ m1_pre_topc(D_445,'#skF_4')
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_4',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_603])).

tff(c_1478,plain,(
    ! [D_445,A_444] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_445)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_4',A_444)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444)
      | ~ m1_pre_topc(D_445,'#skF_4')
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_4',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_16])).

tff(c_1505,plain,(
    ! [D_445,A_444] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_445)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_445,'#skF_4')
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_4',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_578,c_575,c_572,c_1478])).

tff(c_1508,plain,(
    ! [D_446,A_447] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_446)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_446),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_446,'#skF_4')
      | ~ m1_pre_topc(D_446,A_447)
      | ~ m1_pre_topc('#skF_4',A_447)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1505])).

tff(c_1520,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1508])).

tff(c_1540,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_40,c_1520])).

tff(c_1541,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1540])).

tff(c_1564,plain,(
    ! [A_33] :
      ( m1_subset_1(k3_tmap_1(A_33,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_33)
      | ~ m1_pre_topc('#skF_4',A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_1541])).

tff(c_1897,plain,(
    ! [A_453] :
      ( m1_subset_1(k3_tmap_1(A_453,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_3',A_453)
      | ~ m1_pre_topc('#skF_4',A_453)
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453)
      | v2_struct_0(A_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1564])).

tff(c_580,plain,(
    ! [E_364,C_365,D_366,A_363,B_367] :
      ( r2_funct_2(u1_struct_0(C_365),u1_struct_0(B_367),k3_tmap_1(A_363,B_367,D_366,C_365,k2_tmap_1(A_363,B_367,E_364,D_366)),k2_tmap_1(A_363,B_367,E_364,C_365))
      | ~ m1_pre_topc(C_365,D_366)
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0(B_367))))
      | ~ v1_funct_2(E_364,u1_struct_0(A_363),u1_struct_0(B_367))
      | ~ v1_funct_1(E_364)
      | ~ m1_pre_topc(D_366,A_363)
      | v2_struct_0(D_366)
      | ~ m1_pre_topc(C_365,A_363)
      | v2_struct_0(C_365)
      | ~ l1_pre_topc(B_367)
      | ~ v2_pre_topc(B_367)
      | v2_struct_0(B_367)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_583,plain,(
    ! [E_364,C_365,D_366,A_363,B_367] :
      ( k3_tmap_1(A_363,B_367,D_366,C_365,k2_tmap_1(A_363,B_367,E_364,D_366)) = k2_tmap_1(A_363,B_367,E_364,C_365)
      | ~ m1_subset_1(k2_tmap_1(A_363,B_367,E_364,C_365),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_365),u1_struct_0(B_367))))
      | ~ v1_funct_2(k2_tmap_1(A_363,B_367,E_364,C_365),u1_struct_0(C_365),u1_struct_0(B_367))
      | ~ v1_funct_1(k2_tmap_1(A_363,B_367,E_364,C_365))
      | ~ m1_subset_1(k3_tmap_1(A_363,B_367,D_366,C_365,k2_tmap_1(A_363,B_367,E_364,D_366)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_365),u1_struct_0(B_367))))
      | ~ v1_funct_2(k3_tmap_1(A_363,B_367,D_366,C_365,k2_tmap_1(A_363,B_367,E_364,D_366)),u1_struct_0(C_365),u1_struct_0(B_367))
      | ~ v1_funct_1(k3_tmap_1(A_363,B_367,D_366,C_365,k2_tmap_1(A_363,B_367,E_364,D_366)))
      | ~ m1_pre_topc(C_365,D_366)
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0(B_367))))
      | ~ v1_funct_2(E_364,u1_struct_0(A_363),u1_struct_0(B_367))
      | ~ v1_funct_1(E_364)
      | ~ m1_pre_topc(D_366,A_363)
      | v2_struct_0(D_366)
      | ~ m1_pre_topc(C_365,A_363)
      | v2_struct_0(C_365)
      | ~ l1_pre_topc(B_367)
      | ~ v2_pre_topc(B_367)
      | v2_struct_0(B_367)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_580,c_4])).

tff(c_1901,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1897,c_583])).

tff(c_1924,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_52,c_58,c_56,c_46,c_44,c_42,c_40,c_842,c_839,c_836,c_1901])).

tff(c_1925,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_54,c_50,c_1924])).

tff(c_4837,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1925])).

tff(c_4843,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_783,c_4837])).

tff(c_4849,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_52,c_4843])).

tff(c_4851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4849])).

tff(c_4852,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_4861,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4852])).

tff(c_4904,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_923,c_4861])).

tff(c_4910,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_52,c_4904])).

tff(c_4912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4910])).

tff(c_4913,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_4852])).

tff(c_97,plain,(
    ! [B_294,A_295] :
      ( v2_pre_topc(B_294)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_113,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_103])).

tff(c_74,plain,(
    ! [B_292,A_293] :
      ( l1_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_80])).

tff(c_12,plain,(
    ! [A_18,B_26,C_30,D_32] :
      ( k2_partfun1(u1_struct_0(A_18),u1_struct_0(B_26),C_30,u1_struct_0(D_32)) = k2_tmap_1(A_18,B_26,C_30,D_32)
      | ~ m1_pre_topc(D_32,A_18)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18),u1_struct_0(B_26))))
      | ~ v1_funct_2(C_30,u1_struct_0(A_18),u1_struct_0(B_26))
      | ~ v1_funct_1(C_30)
      | ~ l1_pre_topc(B_26)
      | ~ v2_pre_topc(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_592,plain,(
    ! [D_32] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_32)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_32)
      | ~ m1_pre_topc(D_32,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_572,c_12])).

tff(c_611,plain,(
    ! [D_32] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_32)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_32)
      | ~ m1_pre_topc(D_32,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_90,c_58,c_56,c_578,c_575,c_592])).

tff(c_612,plain,(
    ! [D_32] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_32)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_32)
      | ~ m1_pre_topc(D_32,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_60,c_611])).

tff(c_1461,plain,(
    ! [A_444,D_445] :
      ( k3_tmap_1(A_444,'#skF_2','#skF_4',D_445,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_445)
      | ~ m1_pre_topc(D_445,'#skF_4')
      | ~ m1_pre_topc(D_445,'#skF_4')
      | ~ m1_pre_topc(D_445,A_444)
      | ~ m1_pre_topc('#skF_4',A_444)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_612])).

tff(c_4931,plain,
    ( k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4913,c_1461])).

tff(c_4983,plain,
    ( k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_48,c_52,c_40,c_40,c_4931])).

tff(c_4984,plain,(
    k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4983])).

tff(c_428,plain,(
    ! [D_357,C_354,B_358,A_355,F_356] :
      ( r1_tmap_1(D_357,A_355,k2_tmap_1(B_358,A_355,C_354,D_357),F_356)
      | ~ r1_tmap_1(B_358,A_355,C_354,F_356)
      | ~ m1_subset_1(F_356,u1_struct_0(D_357))
      | ~ m1_subset_1(F_356,u1_struct_0(B_358))
      | ~ m1_pre_topc(D_357,B_358)
      | v2_struct_0(D_357)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_358),u1_struct_0(A_355))))
      | ~ v1_funct_2(C_354,u1_struct_0(B_358),u1_struct_0(A_355))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc(B_358)
      | ~ v2_pre_topc(B_358)
      | v2_struct_0(B_358)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_1328,plain,(
    ! [C_423,D_424,D_421,B_422,A_425,E_427,F_426] :
      ( r1_tmap_1(D_424,B_422,k2_tmap_1(D_421,B_422,k3_tmap_1(A_425,B_422,C_423,D_421,E_427),D_424),F_426)
      | ~ r1_tmap_1(D_421,B_422,k3_tmap_1(A_425,B_422,C_423,D_421,E_427),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0(D_424))
      | ~ m1_subset_1(F_426,u1_struct_0(D_421))
      | ~ m1_pre_topc(D_424,D_421)
      | v2_struct_0(D_424)
      | ~ v1_funct_2(k3_tmap_1(A_425,B_422,C_423,D_421,E_427),u1_struct_0(D_421),u1_struct_0(B_422))
      | ~ v1_funct_1(k3_tmap_1(A_425,B_422,C_423,D_421,E_427))
      | ~ l1_pre_topc(D_421)
      | ~ v2_pre_topc(D_421)
      | v2_struct_0(D_421)
      | ~ m1_subset_1(E_427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_423),u1_struct_0(B_422))))
      | ~ v1_funct_2(E_427,u1_struct_0(C_423),u1_struct_0(B_422))
      | ~ v1_funct_1(E_427)
      | ~ m1_pre_topc(D_421,A_425)
      | ~ m1_pre_topc(C_423,A_425)
      | ~ l1_pre_topc(B_422)
      | ~ v2_pre_topc(B_422)
      | v2_struct_0(B_422)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(resolution,[status(thm)],[c_16,c_428])).

tff(c_1344,plain,(
    ! [D_424,F_426] :
      ( r1_tmap_1(D_424,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),D_424),F_426)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0(D_424))
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_424,'#skF_4')
      | v2_struct_0(D_424)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_1328])).

tff(c_1370,plain,(
    ! [D_424,F_426] :
      ( r1_tmap_1(D_424,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_424),F_426)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0(D_424))
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_424,'#skF_4')
      | v2_struct_0(D_424)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_487,c_48,c_46,c_44,c_42,c_113,c_90,c_578,c_553,c_575,c_553,c_553,c_1344])).

tff(c_1371,plain,(
    ! [D_424,F_426] :
      ( r1_tmap_1(D_424,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_424),F_426)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0(D_424))
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_424,'#skF_4')
      | v2_struct_0(D_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_50,c_1370])).

tff(c_5043,plain,(
    ! [F_426] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_426)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4984,c_1371])).

tff(c_5065,plain,(
    ! [F_426] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_426)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_426)
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_426,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5043])).

tff(c_5076,plain,(
    ! [F_556] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_556)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_556)
      | ~ m1_subset_1(F_556,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_556,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5065])).

tff(c_30,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_68,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_5079,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5076,c_68])).

tff(c_5083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_67,c_32,c_5079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.80/3.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.27  
% 9.92/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.27  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.92/3.27  
% 9.92/3.27  %Foreground sorts:
% 9.92/3.27  
% 9.92/3.27  
% 9.92/3.27  %Background operators:
% 9.92/3.27  
% 9.92/3.27  
% 9.92/3.27  %Foreground operators:
% 9.92/3.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.92/3.27  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.92/3.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.92/3.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/3.27  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 9.92/3.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.92/3.27  tff('#skF_7', type, '#skF_7': $i).
% 9.92/3.27  tff('#skF_5', type, '#skF_5': $i).
% 9.92/3.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.92/3.27  tff('#skF_6', type, '#skF_6': $i).
% 9.92/3.27  tff('#skF_2', type, '#skF_2': $i).
% 9.92/3.27  tff('#skF_3', type, '#skF_3': $i).
% 9.92/3.27  tff('#skF_1', type, '#skF_1': $i).
% 9.92/3.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.92/3.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/3.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.92/3.27  tff('#skF_4', type, '#skF_4': $i).
% 9.92/3.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/3.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.92/3.27  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.92/3.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.92/3.27  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.92/3.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.92/3.27  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.92/3.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.92/3.27  
% 9.92/3.31  tff(f_305, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 9.92/3.31  tff(f_166, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.92/3.31  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.92/3.31  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.92/3.31  tff(f_162, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.92/3.31  tff(f_244, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 9.92/3.31  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.92/3.31  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.92/3.31  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.92/3.31  tff(f_206, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 9.92/3.31  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_34, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_67, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 9.92/3.31  tff(c_32, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_22, plain, (![A_69]: (m1_pre_topc(A_69, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.92/3.31  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_418, plain, (![C_353, D_350, E_352, A_349, B_351]: (k3_tmap_1(A_349, B_351, C_353, D_350, E_352)=k2_partfun1(u1_struct_0(C_353), u1_struct_0(B_351), E_352, u1_struct_0(D_350)) | ~m1_pre_topc(D_350, C_353) | ~m1_subset_1(E_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_353), u1_struct_0(B_351)))) | ~v1_funct_2(E_352, u1_struct_0(C_353), u1_struct_0(B_351)) | ~v1_funct_1(E_352) | ~m1_pre_topc(D_350, A_349) | ~m1_pre_topc(C_353, A_349) | ~l1_pre_topc(B_351) | ~v2_pre_topc(B_351) | v2_struct_0(B_351) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.92/3.31  tff(c_422, plain, (![A_349, D_350]: (k3_tmap_1(A_349, '#skF_2', '#skF_1', D_350, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_350)) | ~m1_pre_topc(D_350, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_350, A_349) | ~m1_pre_topc('#skF_1', A_349) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(resolution, [status(thm)], [c_42, c_418])).
% 9.92/3.31  tff(c_426, plain, (![A_349, D_350]: (k3_tmap_1(A_349, '#skF_2', '#skF_1', D_350, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_350)) | ~m1_pre_topc(D_350, '#skF_1') | ~m1_pre_topc(D_350, A_349) | ~m1_pre_topc('#skF_1', A_349) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | v2_struct_0(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_44, c_422])).
% 9.92/3.31  tff(c_446, plain, (![A_361, D_362]: (k3_tmap_1(A_361, '#skF_2', '#skF_1', D_362, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_362)) | ~m1_pre_topc(D_362, '#skF_1') | ~m1_pre_topc(D_362, A_361) | ~m1_pre_topc('#skF_1', A_361) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361) | v2_struct_0(A_361))), inference(negUnitSimplification, [status(thm)], [c_60, c_426])).
% 9.92/3.31  tff(c_454, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_446])).
% 9.92/3.31  tff(c_468, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_454])).
% 9.92/3.31  tff(c_469, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_468])).
% 9.92/3.31  tff(c_478, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_469])).
% 9.92/3.31  tff(c_481, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_478])).
% 9.92/3.31  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_481])).
% 9.92/3.31  tff(c_487, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_469])).
% 9.92/3.31  tff(c_486, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_469])).
% 9.92/3.31  tff(c_381, plain, (![A_332, B_333, C_334, D_335]: (k2_partfun1(u1_struct_0(A_332), u1_struct_0(B_333), C_334, u1_struct_0(D_335))=k2_tmap_1(A_332, B_333, C_334, D_335) | ~m1_pre_topc(D_335, A_332) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332), u1_struct_0(B_333)))) | ~v1_funct_2(C_334, u1_struct_0(A_332), u1_struct_0(B_333)) | ~v1_funct_1(C_334) | ~l1_pre_topc(B_333) | ~v2_pre_topc(B_333) | v2_struct_0(B_333) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.92/3.31  tff(c_383, plain, (![D_335]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_335))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_335) | ~m1_pre_topc(D_335, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_381])).
% 9.92/3.31  tff(c_386, plain, (![D_335]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_335))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_335) | ~m1_pre_topc(D_335, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_46, c_44, c_383])).
% 9.92/3.31  tff(c_387, plain, (![D_335]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_335))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_335) | ~m1_pre_topc(D_335, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_386])).
% 9.92/3.31  tff(c_546, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_486, c_387])).
% 9.92/3.31  tff(c_553, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_546])).
% 9.92/3.31  tff(c_305, plain, (![C_323, D_321, B_322, E_325, A_324]: (v1_funct_1(k3_tmap_1(A_324, B_322, C_323, D_321, E_325)) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323), u1_struct_0(B_322)))) | ~v1_funct_2(E_325, u1_struct_0(C_323), u1_struct_0(B_322)) | ~v1_funct_1(E_325) | ~m1_pre_topc(D_321, A_324) | ~m1_pre_topc(C_323, A_324) | ~l1_pre_topc(B_322) | ~v2_pre_topc(B_322) | v2_struct_0(B_322) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_307, plain, (![A_324, D_321]: (v1_funct_1(k3_tmap_1(A_324, '#skF_2', '#skF_1', D_321, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_321, A_324) | ~m1_pre_topc('#skF_1', A_324) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(resolution, [status(thm)], [c_42, c_305])).
% 9.92/3.31  tff(c_310, plain, (![A_324, D_321]: (v1_funct_1(k3_tmap_1(A_324, '#skF_2', '#skF_1', D_321, '#skF_5')) | ~m1_pre_topc(D_321, A_324) | ~m1_pre_topc('#skF_1', A_324) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_44, c_307])).
% 9.92/3.31  tff(c_311, plain, (![A_324, D_321]: (v1_funct_1(k3_tmap_1(A_324, '#skF_2', '#skF_1', D_321, '#skF_5')) | ~m1_pre_topc(D_321, A_324) | ~m1_pre_topc('#skF_1', A_324) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(negUnitSimplification, [status(thm)], [c_60, c_310])).
% 9.92/3.31  tff(c_567, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_553, c_311])).
% 9.92/3.31  tff(c_577, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_487, c_48, c_567])).
% 9.92/3.31  tff(c_578, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_577])).
% 9.92/3.31  tff(c_397, plain, (![B_338, C_339, E_341, D_337, A_340]: (v1_funct_2(k3_tmap_1(A_340, B_338, C_339, D_337, E_341), u1_struct_0(D_337), u1_struct_0(B_338)) | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_339), u1_struct_0(B_338)))) | ~v1_funct_2(E_341, u1_struct_0(C_339), u1_struct_0(B_338)) | ~v1_funct_1(E_341) | ~m1_pre_topc(D_337, A_340) | ~m1_pre_topc(C_339, A_340) | ~l1_pre_topc(B_338) | ~v2_pre_topc(B_338) | v2_struct_0(B_338) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_399, plain, (![A_340, D_337]: (v1_funct_2(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_337, '#skF_5'), u1_struct_0(D_337), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_337, A_340) | ~m1_pre_topc('#skF_1', A_340) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_42, c_397])).
% 9.92/3.31  tff(c_402, plain, (![A_340, D_337]: (v1_funct_2(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_337, '#skF_5'), u1_struct_0(D_337), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_337, A_340) | ~m1_pre_topc('#skF_1', A_340) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_44, c_399])).
% 9.92/3.31  tff(c_403, plain, (![A_340, D_337]: (v1_funct_2(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_337, '#skF_5'), u1_struct_0(D_337), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_337, A_340) | ~m1_pre_topc('#skF_1', A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(negUnitSimplification, [status(thm)], [c_60, c_402])).
% 9.92/3.31  tff(c_564, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_553, c_403])).
% 9.92/3.31  tff(c_574, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_487, c_48, c_564])).
% 9.92/3.31  tff(c_575, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_574])).
% 9.92/3.31  tff(c_405, plain, (![B_345, A_347, D_344, C_346, E_348]: (m1_subset_1(k3_tmap_1(A_347, B_345, C_346, D_344, E_348), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344), u1_struct_0(B_345)))) | ~m1_subset_1(E_348, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346), u1_struct_0(B_345)))) | ~v1_funct_2(E_348, u1_struct_0(C_346), u1_struct_0(B_345)) | ~v1_funct_1(E_348) | ~m1_pre_topc(D_344, A_347) | ~m1_pre_topc(C_346, A_347) | ~l1_pre_topc(B_345) | ~v2_pre_topc(B_345) | v2_struct_0(B_345) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_18, plain, (![D_67, E_68, C_66, A_64, B_65]: (v1_funct_2(k3_tmap_1(A_64, B_65, C_66, D_67, E_68), u1_struct_0(D_67), u1_struct_0(B_65)) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66), u1_struct_0(B_65)))) | ~v1_funct_2(E_68, u1_struct_0(C_66), u1_struct_0(B_65)) | ~v1_funct_1(E_68) | ~m1_pre_topc(D_67, A_64) | ~m1_pre_topc(C_66, A_64) | ~l1_pre_topc(B_65) | ~v2_pre_topc(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_902, plain, (![B_386, C_381, D_383, A_385, D_380, E_384, A_382]: (v1_funct_2(k3_tmap_1(A_385, B_386, D_383, D_380, k3_tmap_1(A_382, B_386, C_381, D_383, E_384)), u1_struct_0(D_380), u1_struct_0(B_386)) | ~v1_funct_2(k3_tmap_1(A_382, B_386, C_381, D_383, E_384), u1_struct_0(D_383), u1_struct_0(B_386)) | ~v1_funct_1(k3_tmap_1(A_382, B_386, C_381, D_383, E_384)) | ~m1_pre_topc(D_380, A_385) | ~m1_pre_topc(D_383, A_385) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381), u1_struct_0(B_386)))) | ~v1_funct_2(E_384, u1_struct_0(C_381), u1_struct_0(B_386)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_383, A_382) | ~m1_pre_topc(C_381, A_382) | ~l1_pre_topc(B_386) | ~v2_pre_topc(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(resolution, [status(thm)], [c_405, c_18])).
% 9.92/3.31  tff(c_913, plain, (![A_385, D_380]: (v1_funct_2(k3_tmap_1(A_385, '#skF_2', '#skF_4', D_380, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_380), u1_struct_0('#skF_2')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_380, A_385) | ~m1_pre_topc('#skF_4', A_385) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_902])).
% 9.92/3.31  tff(c_922, plain, (![A_385, D_380]: (v1_funct_2(k3_tmap_1(A_385, '#skF_2', '#skF_4', D_380, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_380), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_380, A_385) | ~m1_pre_topc('#skF_4', A_385) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_487, c_48, c_46, c_44, c_42, c_578, c_553, c_575, c_553, c_913])).
% 9.92/3.31  tff(c_923, plain, (![A_385, D_380]: (v1_funct_2(k3_tmap_1(A_385, '#skF_2', '#skF_4', D_380, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_380), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_380, A_385) | ~m1_pre_topc('#skF_4', A_385) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_922])).
% 9.92/3.31  tff(c_20, plain, (![D_67, E_68, C_66, A_64, B_65]: (v1_funct_1(k3_tmap_1(A_64, B_65, C_66, D_67, E_68)) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66), u1_struct_0(B_65)))) | ~v1_funct_2(E_68, u1_struct_0(C_66), u1_struct_0(B_65)) | ~v1_funct_1(E_68) | ~m1_pre_topc(D_67, A_64) | ~m1_pre_topc(C_66, A_64) | ~l1_pre_topc(B_65) | ~v2_pre_topc(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_771, plain, (![D_376, A_375, B_379, D_373, A_378, E_377, C_374]: (v1_funct_1(k3_tmap_1(A_378, B_379, D_376, D_373, k3_tmap_1(A_375, B_379, C_374, D_376, E_377))) | ~v1_funct_2(k3_tmap_1(A_375, B_379, C_374, D_376, E_377), u1_struct_0(D_376), u1_struct_0(B_379)) | ~v1_funct_1(k3_tmap_1(A_375, B_379, C_374, D_376, E_377)) | ~m1_pre_topc(D_373, A_378) | ~m1_pre_topc(D_376, A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378) | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_374), u1_struct_0(B_379)))) | ~v1_funct_2(E_377, u1_struct_0(C_374), u1_struct_0(B_379)) | ~v1_funct_1(E_377) | ~m1_pre_topc(D_376, A_375) | ~m1_pre_topc(C_374, A_375) | ~l1_pre_topc(B_379) | ~v2_pre_topc(B_379) | v2_struct_0(B_379) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(resolution, [status(thm)], [c_405, c_20])).
% 9.92/3.31  tff(c_775, plain, (![A_378, D_373]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_4', D_373, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_373, A_378) | ~m1_pre_topc('#skF_4', A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_771])).
% 9.92/3.31  tff(c_782, plain, (![A_378, D_373]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_4', D_373, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_373, A_378) | ~m1_pre_topc('#skF_4', A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_487, c_48, c_46, c_44, c_42, c_578, c_553, c_575, c_553, c_775])).
% 9.92/3.31  tff(c_783, plain, (![A_378, D_373]: (v1_funct_1(k3_tmap_1(A_378, '#skF_2', '#skF_4', D_373, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_373, A_378) | ~m1_pre_topc('#skF_4', A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378) | v2_struct_0(A_378))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_782])).
% 9.92/3.31  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_456, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_446])).
% 9.92/3.31  tff(c_472, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_52, c_456])).
% 9.92/3.31  tff(c_473, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_472])).
% 9.92/3.31  tff(c_789, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_473])).
% 9.92/3.31  tff(c_793, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_789, c_387])).
% 9.92/3.31  tff(c_800, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_793])).
% 9.92/3.31  tff(c_822, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_800, c_311])).
% 9.92/3.31  tff(c_841, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_487, c_52, c_822])).
% 9.92/3.31  tff(c_842, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_841])).
% 9.92/3.31  tff(c_819, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_800, c_403])).
% 9.92/3.31  tff(c_838, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_487, c_52, c_819])).
% 9.92/3.31  tff(c_839, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_838])).
% 9.92/3.31  tff(c_16, plain, (![D_67, E_68, C_66, A_64, B_65]: (m1_subset_1(k3_tmap_1(A_64, B_65, C_66, D_67, E_68), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_67), u1_struct_0(B_65)))) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_66), u1_struct_0(B_65)))) | ~v1_funct_2(E_68, u1_struct_0(C_66), u1_struct_0(B_65)) | ~v1_funct_1(E_68) | ~m1_pre_topc(D_67, A_64) | ~m1_pre_topc(C_66, A_64) | ~l1_pre_topc(B_65) | ~v2_pre_topc(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.92/3.31  tff(c_816, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_800, c_16])).
% 9.92/3.31  tff(c_835, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_487, c_52, c_46, c_44, c_42, c_816])).
% 9.92/3.31  tff(c_836, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_835])).
% 9.92/3.31  tff(c_561, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_553, c_16])).
% 9.92/3.31  tff(c_571, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_487, c_48, c_46, c_44, c_42, c_561])).
% 9.92/3.31  tff(c_572, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_571])).
% 9.92/3.31  tff(c_14, plain, (![B_49, C_57, D_61, A_33, E_63]: (k3_tmap_1(A_33, B_49, C_57, D_61, E_63)=k2_partfun1(u1_struct_0(C_57), u1_struct_0(B_49), E_63, u1_struct_0(D_61)) | ~m1_pre_topc(D_61, C_57) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_57), u1_struct_0(B_49)))) | ~v1_funct_2(E_63, u1_struct_0(C_57), u1_struct_0(B_49)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_61, A_33) | ~m1_pre_topc(C_57, A_33) | ~l1_pre_topc(B_49) | ~v2_pre_topc(B_49) | v2_struct_0(B_49) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.92/3.31  tff(c_588, plain, (![A_33, D_61]: (k3_tmap_1(A_33, '#skF_2', '#skF_4', D_61, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_61)) | ~m1_pre_topc(D_61, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_61, A_33) | ~m1_pre_topc('#skF_4', A_33) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(resolution, [status(thm)], [c_572, c_14])).
% 9.92/3.31  tff(c_603, plain, (![A_33, D_61]: (k3_tmap_1(A_33, '#skF_2', '#skF_4', D_61, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_61)) | ~m1_pre_topc(D_61, '#skF_4') | ~m1_pre_topc(D_61, A_33) | ~m1_pre_topc('#skF_4', A_33) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_578, c_575, c_588])).
% 9.92/3.31  tff(c_604, plain, (![A_33, D_61]: (k3_tmap_1(A_33, '#skF_2', '#skF_4', D_61, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_61)) | ~m1_pre_topc(D_61, '#skF_4') | ~m1_pre_topc(D_61, A_33) | ~m1_pre_topc('#skF_4', A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(negUnitSimplification, [status(thm)], [c_60, c_603])).
% 9.92/3.31  tff(c_1447, plain, (![A_444, D_445]: (k3_tmap_1(A_444, '#skF_2', '#skF_4', D_445, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_445)) | ~m1_pre_topc(D_445, '#skF_4') | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_4', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(negUnitSimplification, [status(thm)], [c_60, c_603])).
% 9.92/3.31  tff(c_1478, plain, (![D_445, A_444]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_445)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_4', A_444) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444) | ~m1_pre_topc(D_445, '#skF_4') | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_4', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_16])).
% 9.92/3.31  tff(c_1505, plain, (![D_445, A_444]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_445)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_445, '#skF_4') | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_4', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_578, c_575, c_572, c_1478])).
% 9.92/3.31  tff(c_1508, plain, (![D_446, A_447]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_446)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_446), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_446, '#skF_4') | ~m1_pre_topc(D_446, A_447) | ~m1_pre_topc('#skF_4', A_447) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447))), inference(negUnitSimplification, [status(thm)], [c_60, c_1505])).
% 9.92/3.31  tff(c_1520, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1508])).
% 9.92/3.31  tff(c_1540, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_40, c_1520])).
% 9.92/3.31  tff(c_1541, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_1540])).
% 9.92/3.31  tff(c_1564, plain, (![A_33]: (m1_subset_1(k3_tmap_1(A_33, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', A_33) | ~m1_pre_topc('#skF_4', A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(superposition, [status(thm), theory('equality')], [c_604, c_1541])).
% 9.92/3.31  tff(c_1897, plain, (![A_453]: (m1_subset_1(k3_tmap_1(A_453, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', A_453) | ~m1_pre_topc('#skF_4', A_453) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453) | v2_struct_0(A_453))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1564])).
% 9.92/3.31  tff(c_580, plain, (![E_364, C_365, D_366, A_363, B_367]: (r2_funct_2(u1_struct_0(C_365), u1_struct_0(B_367), k3_tmap_1(A_363, B_367, D_366, C_365, k2_tmap_1(A_363, B_367, E_364, D_366)), k2_tmap_1(A_363, B_367, E_364, C_365)) | ~m1_pre_topc(C_365, D_366) | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0(B_367)))) | ~v1_funct_2(E_364, u1_struct_0(A_363), u1_struct_0(B_367)) | ~v1_funct_1(E_364) | ~m1_pre_topc(D_366, A_363) | v2_struct_0(D_366) | ~m1_pre_topc(C_365, A_363) | v2_struct_0(C_365) | ~l1_pre_topc(B_367) | ~v2_pre_topc(B_367) | v2_struct_0(B_367) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(cnfTransformation, [status(thm)], [f_244])).
% 9.92/3.31  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.92/3.31  tff(c_583, plain, (![E_364, C_365, D_366, A_363, B_367]: (k3_tmap_1(A_363, B_367, D_366, C_365, k2_tmap_1(A_363, B_367, E_364, D_366))=k2_tmap_1(A_363, B_367, E_364, C_365) | ~m1_subset_1(k2_tmap_1(A_363, B_367, E_364, C_365), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_365), u1_struct_0(B_367)))) | ~v1_funct_2(k2_tmap_1(A_363, B_367, E_364, C_365), u1_struct_0(C_365), u1_struct_0(B_367)) | ~v1_funct_1(k2_tmap_1(A_363, B_367, E_364, C_365)) | ~m1_subset_1(k3_tmap_1(A_363, B_367, D_366, C_365, k2_tmap_1(A_363, B_367, E_364, D_366)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_365), u1_struct_0(B_367)))) | ~v1_funct_2(k3_tmap_1(A_363, B_367, D_366, C_365, k2_tmap_1(A_363, B_367, E_364, D_366)), u1_struct_0(C_365), u1_struct_0(B_367)) | ~v1_funct_1(k3_tmap_1(A_363, B_367, D_366, C_365, k2_tmap_1(A_363, B_367, E_364, D_366))) | ~m1_pre_topc(C_365, D_366) | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0(B_367)))) | ~v1_funct_2(E_364, u1_struct_0(A_363), u1_struct_0(B_367)) | ~v1_funct_1(E_364) | ~m1_pre_topc(D_366, A_363) | v2_struct_0(D_366) | ~m1_pre_topc(C_365, A_363) | v2_struct_0(C_365) | ~l1_pre_topc(B_367) | ~v2_pre_topc(B_367) | v2_struct_0(B_367) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_580, c_4])).
% 9.92/3.31  tff(c_1901, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1897, c_583])).
% 9.92/3.31  tff(c_1924, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_52, c_58, c_56, c_46, c_44, c_42, c_40, c_842, c_839, c_836, c_1901])).
% 9.92/3.31  tff(c_1925, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_54, c_50, c_1924])).
% 9.92/3.31  tff(c_4837, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1925])).
% 9.92/3.31  tff(c_4843, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_783, c_4837])).
% 9.92/3.31  tff(c_4849, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_52, c_4843])).
% 9.92/3.31  tff(c_4851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4849])).
% 9.92/3.31  tff(c_4852, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1925])).
% 9.92/3.31  tff(c_4861, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4852])).
% 9.92/3.31  tff(c_4904, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_923, c_4861])).
% 9.92/3.31  tff(c_4910, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_52, c_4904])).
% 9.92/3.31  tff(c_4912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4910])).
% 9.92/3.31  tff(c_4913, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_4852])).
% 9.92/3.31  tff(c_97, plain, (![B_294, A_295]: (v2_pre_topc(B_294) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.92/3.31  tff(c_103, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_97])).
% 9.92/3.31  tff(c_113, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_103])).
% 9.92/3.31  tff(c_74, plain, (![B_292, A_293]: (l1_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.92/3.31  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_74])).
% 9.92/3.31  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_80])).
% 9.92/3.31  tff(c_12, plain, (![A_18, B_26, C_30, D_32]: (k2_partfun1(u1_struct_0(A_18), u1_struct_0(B_26), C_30, u1_struct_0(D_32))=k2_tmap_1(A_18, B_26, C_30, D_32) | ~m1_pre_topc(D_32, A_18) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_18), u1_struct_0(B_26)))) | ~v1_funct_2(C_30, u1_struct_0(A_18), u1_struct_0(B_26)) | ~v1_funct_1(C_30) | ~l1_pre_topc(B_26) | ~v2_pre_topc(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.92/3.31  tff(c_592, plain, (![D_32]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_32))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_32) | ~m1_pre_topc(D_32, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_572, c_12])).
% 9.92/3.31  tff(c_611, plain, (![D_32]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_32))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_32) | ~m1_pre_topc(D_32, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_90, c_58, c_56, c_578, c_575, c_592])).
% 9.92/3.31  tff(c_612, plain, (![D_32]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_32))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_32) | ~m1_pre_topc(D_32, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_60, c_611])).
% 9.92/3.31  tff(c_1461, plain, (![A_444, D_445]: (k3_tmap_1(A_444, '#skF_2', '#skF_4', D_445, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_445) | ~m1_pre_topc(D_445, '#skF_4') | ~m1_pre_topc(D_445, '#skF_4') | ~m1_pre_topc(D_445, A_444) | ~m1_pre_topc('#skF_4', A_444) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_612])).
% 9.92/3.31  tff(c_4931, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4913, c_1461])).
% 9.92/3.31  tff(c_4983, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_48, c_52, c_40, c_40, c_4931])).
% 9.92/3.31  tff(c_4984, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_66, c_4983])).
% 9.92/3.31  tff(c_428, plain, (![D_357, C_354, B_358, A_355, F_356]: (r1_tmap_1(D_357, A_355, k2_tmap_1(B_358, A_355, C_354, D_357), F_356) | ~r1_tmap_1(B_358, A_355, C_354, F_356) | ~m1_subset_1(F_356, u1_struct_0(D_357)) | ~m1_subset_1(F_356, u1_struct_0(B_358)) | ~m1_pre_topc(D_357, B_358) | v2_struct_0(D_357) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_358), u1_struct_0(A_355)))) | ~v1_funct_2(C_354, u1_struct_0(B_358), u1_struct_0(A_355)) | ~v1_funct_1(C_354) | ~l1_pre_topc(B_358) | ~v2_pre_topc(B_358) | v2_struct_0(B_358) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.92/3.31  tff(c_1328, plain, (![C_423, D_424, D_421, B_422, A_425, E_427, F_426]: (r1_tmap_1(D_424, B_422, k2_tmap_1(D_421, B_422, k3_tmap_1(A_425, B_422, C_423, D_421, E_427), D_424), F_426) | ~r1_tmap_1(D_421, B_422, k3_tmap_1(A_425, B_422, C_423, D_421, E_427), F_426) | ~m1_subset_1(F_426, u1_struct_0(D_424)) | ~m1_subset_1(F_426, u1_struct_0(D_421)) | ~m1_pre_topc(D_424, D_421) | v2_struct_0(D_424) | ~v1_funct_2(k3_tmap_1(A_425, B_422, C_423, D_421, E_427), u1_struct_0(D_421), u1_struct_0(B_422)) | ~v1_funct_1(k3_tmap_1(A_425, B_422, C_423, D_421, E_427)) | ~l1_pre_topc(D_421) | ~v2_pre_topc(D_421) | v2_struct_0(D_421) | ~m1_subset_1(E_427, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_423), u1_struct_0(B_422)))) | ~v1_funct_2(E_427, u1_struct_0(C_423), u1_struct_0(B_422)) | ~v1_funct_1(E_427) | ~m1_pre_topc(D_421, A_425) | ~m1_pre_topc(C_423, A_425) | ~l1_pre_topc(B_422) | ~v2_pre_topc(B_422) | v2_struct_0(B_422) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(resolution, [status(thm)], [c_16, c_428])).
% 9.92/3.31  tff(c_1344, plain, (![D_424, F_426]: (r1_tmap_1(D_424, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), D_424), F_426) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), F_426) | ~m1_subset_1(F_426, u1_struct_0(D_424)) | ~m1_subset_1(F_426, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_424, '#skF_4') | v2_struct_0(D_424) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_553, c_1328])).
% 9.92/3.31  tff(c_1370, plain, (![D_424, F_426]: (r1_tmap_1(D_424, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_424), F_426) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_426) | ~m1_subset_1(F_426, u1_struct_0(D_424)) | ~m1_subset_1(F_426, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_424, '#skF_4') | v2_struct_0(D_424) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_487, c_48, c_46, c_44, c_42, c_113, c_90, c_578, c_553, c_575, c_553, c_553, c_1344])).
% 9.92/3.31  tff(c_1371, plain, (![D_424, F_426]: (r1_tmap_1(D_424, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_424), F_426) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_426) | ~m1_subset_1(F_426, u1_struct_0(D_424)) | ~m1_subset_1(F_426, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_424, '#skF_4') | v2_struct_0(D_424))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_50, c_1370])).
% 9.92/3.31  tff(c_5043, plain, (![F_426]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_426) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_426) | ~m1_subset_1(F_426, u1_struct_0('#skF_3')) | ~m1_subset_1(F_426, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4984, c_1371])).
% 9.92/3.31  tff(c_5065, plain, (![F_426]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_426) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_426) | ~m1_subset_1(F_426, u1_struct_0('#skF_3')) | ~m1_subset_1(F_426, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5043])).
% 9.92/3.31  tff(c_5076, plain, (![F_556]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_556) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_556) | ~m1_subset_1(F_556, u1_struct_0('#skF_3')) | ~m1_subset_1(F_556, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_5065])).
% 9.92/3.31  tff(c_30, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_305])).
% 9.92/3.31  tff(c_68, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 9.92/3.31  tff(c_5079, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5076, c_68])).
% 9.92/3.31  tff(c_5083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_67, c_32, c_5079])).
% 9.92/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.31  
% 9.92/3.31  Inference rules
% 9.92/3.31  ----------------------
% 9.92/3.31  #Ref     : 0
% 9.92/3.31  #Sup     : 932
% 9.92/3.31  #Fact    : 0
% 9.92/3.31  #Define  : 0
% 9.92/3.31  #Split   : 8
% 9.92/3.31  #Chain   : 0
% 9.92/3.31  #Close   : 0
% 9.92/3.31  
% 9.92/3.31  Ordering : KBO
% 9.92/3.31  
% 9.92/3.31  Simplification rules
% 9.92/3.31  ----------------------
% 9.92/3.31  #Subsume      : 129
% 9.92/3.31  #Demod        : 3097
% 9.92/3.31  #Tautology    : 199
% 9.92/3.31  #SimpNegUnit  : 590
% 9.92/3.31  #BackRed      : 6
% 9.92/3.31  
% 9.92/3.31  #Partial instantiations: 0
% 9.92/3.31  #Strategies tried      : 1
% 9.92/3.31  
% 9.92/3.31  Timing (in seconds)
% 9.92/3.31  ----------------------
% 9.92/3.32  Preprocessing        : 0.43
% 9.92/3.32  Parsing              : 0.23
% 9.92/3.32  CNF conversion       : 0.05
% 9.92/3.32  Main loop            : 2.07
% 9.92/3.32  Inferencing          : 0.54
% 9.92/3.32  Reduction            : 0.83
% 9.92/3.32  Demodulation         : 0.65
% 9.92/3.32  BG Simplification    : 0.09
% 9.92/3.32  Subsumption          : 0.50
% 9.92/3.32  Abstraction          : 0.13
% 9.92/3.32  MUC search           : 0.00
% 9.92/3.32  Cooper               : 0.00
% 9.92/3.32  Total                : 2.58
% 9.92/3.32  Index Insertion      : 0.00
% 9.92/3.32  Index Deletion       : 0.00
% 9.92/3.32  Index Matching       : 0.00
% 9.92/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
