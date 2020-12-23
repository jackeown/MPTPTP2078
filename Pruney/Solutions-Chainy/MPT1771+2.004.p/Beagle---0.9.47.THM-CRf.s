%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  156 (5935 expanded)
%              Number of leaves         :   33 (2362 expanded)
%              Depth                    :   34
%              Number of atoms          :  815 (54472 expanded)
%              Number of equality atoms :   38 (3349 expanded)
%              Maximal formula depth    :   34 (   7 average)
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

tff(f_281,negated_conjecture,(
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

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_68,axiom,(
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

tff(f_130,axiom,(
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

tff(f_172,axiom,(
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

tff(f_232,axiom,(
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

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_28,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_61,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_26,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_16,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_203,plain,(
    ! [A_386,D_385,B_387,C_388,E_384] :
      ( k3_tmap_1(A_386,B_387,C_388,D_385,E_384) = k2_partfun1(u1_struct_0(C_388),u1_struct_0(B_387),E_384,u1_struct_0(D_385))
      | ~ m1_pre_topc(D_385,C_388)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_388),u1_struct_0(B_387))))
      | ~ v1_funct_2(E_384,u1_struct_0(C_388),u1_struct_0(B_387))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_385,A_386)
      | ~ m1_pre_topc(C_388,A_386)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_207,plain,(
    ! [A_386,D_385] :
      ( k3_tmap_1(A_386,'#skF_2','#skF_1',D_385,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_385))
      | ~ m1_pre_topc(D_385,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_385,A_386)
      | ~ m1_pre_topc('#skF_1',A_386)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(resolution,[status(thm)],[c_36,c_203])).

tff(c_211,plain,(
    ! [A_386,D_385] :
      ( k3_tmap_1(A_386,'#skF_2','#skF_1',D_385,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_385))
      | ~ m1_pre_topc(D_385,'#skF_1')
      | ~ m1_pre_topc(D_385,A_386)
      | ~ m1_pre_topc('#skF_1',A_386)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_207])).

tff(c_213,plain,(
    ! [A_389,D_390] :
      ( k3_tmap_1(A_389,'#skF_2','#skF_1',D_390,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_390))
      | ~ m1_pre_topc(D_390,'#skF_1')
      | ~ m1_pre_topc(D_390,A_389)
      | ~ m1_pre_topc('#skF_1',A_389)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_211])).

tff(c_221,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_213])).

tff(c_235,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_221])).

tff(c_236,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_235])).

tff(c_245,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_249,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_245])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_249])).

tff(c_255,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_254,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_166,plain,(
    ! [A_367,B_368,C_369,D_370] :
      ( k2_partfun1(u1_struct_0(A_367),u1_struct_0(B_368),C_369,u1_struct_0(D_370)) = k2_tmap_1(A_367,B_368,C_369,D_370)
      | ~ m1_pre_topc(D_370,A_367)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_367),u1_struct_0(B_368))))
      | ~ v1_funct_2(C_369,u1_struct_0(A_367),u1_struct_0(B_368))
      | ~ v1_funct_1(C_369)
      | ~ l1_pre_topc(B_368)
      | ~ v2_pre_topc(B_368)
      | v2_struct_0(B_368)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_168,plain,(
    ! [D_370] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_370)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_370)
      | ~ m1_pre_topc(D_370,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_171,plain,(
    ! [D_370] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_370)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_370)
      | ~ m1_pre_topc(D_370,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_40,c_38,c_168])).

tff(c_172,plain,(
    ! [D_370] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_370)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_370)
      | ~ m1_pre_topc(D_370,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_171])).

tff(c_284,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_172])).

tff(c_291,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_284])).

tff(c_158,plain,(
    ! [E_364,B_361,D_363,C_362,A_360] :
      ( v1_funct_1(k3_tmap_1(A_360,B_361,C_362,D_363,E_364))
      | ~ m1_subset_1(E_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_362),u1_struct_0(B_361))))
      | ~ v1_funct_2(E_364,u1_struct_0(C_362),u1_struct_0(B_361))
      | ~ v1_funct_1(E_364)
      | ~ m1_pre_topc(D_363,A_360)
      | ~ m1_pre_topc(C_362,A_360)
      | ~ l1_pre_topc(B_361)
      | ~ v2_pre_topc(B_361)
      | v2_struct_0(B_361)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_160,plain,(
    ! [A_360,D_363] :
      ( v1_funct_1(k3_tmap_1(A_360,'#skF_2','#skF_1',D_363,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_363,A_360)
      | ~ m1_pre_topc('#skF_1',A_360)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_163,plain,(
    ! [A_360,D_363] :
      ( v1_funct_1(k3_tmap_1(A_360,'#skF_2','#skF_1',D_363,'#skF_5'))
      | ~ m1_pre_topc(D_363,A_360)
      | ~ m1_pre_topc('#skF_1',A_360)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_160])).

tff(c_164,plain,(
    ! [A_360,D_363] :
      ( v1_funct_1(k3_tmap_1(A_360,'#skF_2','#skF_1',D_363,'#skF_5'))
      | ~ m1_pre_topc(D_363,A_360)
      | ~ m1_pre_topc('#skF_1',A_360)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_305,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_164])).

tff(c_315,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_42,c_305])).

tff(c_316,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_315])).

tff(c_182,plain,(
    ! [A_372,E_376,D_375,C_374,B_373] :
      ( v1_funct_2(k3_tmap_1(A_372,B_373,C_374,D_375,E_376),u1_struct_0(D_375),u1_struct_0(B_373))
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_374),u1_struct_0(B_373))))
      | ~ v1_funct_2(E_376,u1_struct_0(C_374),u1_struct_0(B_373))
      | ~ v1_funct_1(E_376)
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc(C_374,A_372)
      | ~ l1_pre_topc(B_373)
      | ~ v2_pre_topc(B_373)
      | v2_struct_0(B_373)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_184,plain,(
    ! [A_372,D_375] :
      ( v1_funct_2(k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'),u1_struct_0(D_375),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc('#skF_1',A_372)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_187,plain,(
    ! [A_372,D_375] :
      ( v1_funct_2(k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'),u1_struct_0(D_375),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc('#skF_1',A_372)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_184])).

tff(c_188,plain,(
    ! [A_372,D_375] :
      ( v1_funct_2(k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'),u1_struct_0(D_375),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc('#skF_1',A_372)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_187])).

tff(c_302,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_188])).

tff(c_312,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_42,c_302])).

tff(c_313,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_312])).

tff(c_10,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( m1_subset_1(k3_tmap_1(A_51,B_52,C_53,D_54,E_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54),u1_struct_0(B_52))))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_299,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_291,c_10])).

tff(c_309,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_42,c_40,c_38,c_36,c_299])).

tff(c_310,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_309])).

tff(c_12,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( v1_funct_2(k3_tmap_1(A_51,B_52,C_53,D_54,E_55),u1_struct_0(D_54),u1_struct_0(B_52))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_326,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_310,c_12])).

tff(c_339,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_326])).

tff(c_340,plain,(
    ! [A_51,D_54] :
      ( v1_funct_2(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_54),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_339])).

tff(c_14,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( v1_funct_1(k3_tmap_1(A_51,B_52,C_53,D_54,E_55))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0(B_52))))
      | ~ v1_funct_2(E_55,u1_struct_0(C_53),u1_struct_0(B_52))
      | ~ v1_funct_1(E_55)
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc(C_53,A_51)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_330,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_310,c_14])).

tff(c_347,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_330])).

tff(c_348,plain,(
    ! [A_51,D_54] :
      ( v1_funct_1(k3_tmap_1(A_51,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_54,A_51)
      | ~ m1_pre_topc('#skF_4',A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_347])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_223,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_213])).

tff(c_239,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_223])).

tff(c_240,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_239])).

tff(c_480,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_240])).

tff(c_484,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_172])).

tff(c_491,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_484])).

tff(c_505,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_164])).

tff(c_515,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_46,c_505])).

tff(c_516,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_515])).

tff(c_502,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_188])).

tff(c_512,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_46,c_502])).

tff(c_513,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_512])).

tff(c_499,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_491,c_10])).

tff(c_509,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_255,c_46,c_40,c_38,c_36,c_499])).

tff(c_510,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_509])).

tff(c_8,plain,(
    ! [E_50,D_48,B_36,A_20,C_44] :
      ( k3_tmap_1(A_20,B_36,C_44,D_48,E_50) = k2_partfun1(u1_struct_0(C_44),u1_struct_0(B_36),E_50,u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,C_44)
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_44),u1_struct_0(B_36))))
      | ~ v1_funct_2(E_50,u1_struct_0(C_44),u1_struct_0(B_36))
      | ~ v1_funct_1(E_50)
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc(C_44,A_20)
      | ~ l1_pre_topc(B_36)
      | ~ v2_pre_topc(B_36)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_324,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_310,c_8])).

tff(c_335,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_324])).

tff(c_336,plain,(
    ! [A_20,D_48] :
      ( k3_tmap_1(A_20,'#skF_2','#skF_4',D_48,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_48))
      | ~ m1_pre_topc(D_48,'#skF_4')
      | ~ m1_pre_topc(D_48,A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_335])).

tff(c_1293,plain,(
    ! [A_469,D_470] :
      ( k3_tmap_1(A_469,'#skF_2','#skF_4',D_470,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_470))
      | ~ m1_pre_topc(D_470,'#skF_4')
      | ~ m1_pre_topc(D_470,A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_335])).

tff(c_1319,plain,(
    ! [D_470,A_469] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_470)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_470),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_470,A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469)
      | ~ m1_pre_topc(D_470,'#skF_4')
      | ~ m1_pre_topc(D_470,A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_10])).

tff(c_1340,plain,(
    ! [D_470,A_469] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_470)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_470),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_470,'#skF_4')
      | ~ m1_pre_topc(D_470,A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_316,c_313,c_310,c_1319])).

tff(c_1343,plain,(
    ! [D_471,A_472] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_471)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_471),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_471,'#skF_4')
      | ~ m1_pre_topc(D_471,A_472)
      | ~ m1_pre_topc('#skF_4',A_472)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1340])).

tff(c_1355,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1343])).

tff(c_1375,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_1355])).

tff(c_1376,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1375])).

tff(c_1399,plain,(
    ! [A_20] :
      ( m1_subset_1(k3_tmap_1(A_20,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1376])).

tff(c_1430,plain,(
    ! [A_20] :
      ( m1_subset_1(k3_tmap_1(A_20,'#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc('#skF_3',A_20)
      | ~ m1_pre_topc('#skF_4',A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1399])).

tff(c_318,plain,(
    ! [D_392,C_393,A_395,E_394,B_391] :
      ( r2_funct_2(u1_struct_0(C_393),u1_struct_0(B_391),k3_tmap_1(A_395,B_391,D_392,C_393,k2_tmap_1(A_395,B_391,E_394,D_392)),k2_tmap_1(A_395,B_391,E_394,C_393))
      | ~ m1_pre_topc(C_393,D_392)
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_391))))
      | ~ v1_funct_2(E_394,u1_struct_0(A_395),u1_struct_0(B_391))
      | ~ v1_funct_1(E_394)
      | ~ m1_pre_topc(D_392,A_395)
      | v2_struct_0(D_392)
      | ~ m1_pre_topc(C_393,A_395)
      | v2_struct_0(C_393)
      | ~ l1_pre_topc(B_391)
      | ~ v2_pre_topc(B_391)
      | v2_struct_0(B_391)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

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

tff(c_1852,plain,(
    ! [C_487,D_490,B_489,E_491,A_488] :
      ( k3_tmap_1(A_488,B_489,D_490,C_487,k2_tmap_1(A_488,B_489,E_491,D_490)) = k2_tmap_1(A_488,B_489,E_491,C_487)
      | ~ m1_subset_1(k2_tmap_1(A_488,B_489,E_491,C_487),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_487),u1_struct_0(B_489))))
      | ~ v1_funct_2(k2_tmap_1(A_488,B_489,E_491,C_487),u1_struct_0(C_487),u1_struct_0(B_489))
      | ~ v1_funct_1(k2_tmap_1(A_488,B_489,E_491,C_487))
      | ~ m1_subset_1(k3_tmap_1(A_488,B_489,D_490,C_487,k2_tmap_1(A_488,B_489,E_491,D_490)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_487),u1_struct_0(B_489))))
      | ~ v1_funct_2(k3_tmap_1(A_488,B_489,D_490,C_487,k2_tmap_1(A_488,B_489,E_491,D_490)),u1_struct_0(C_487),u1_struct_0(B_489))
      | ~ v1_funct_1(k3_tmap_1(A_488,B_489,D_490,C_487,k2_tmap_1(A_488,B_489,E_491,D_490)))
      | ~ m1_pre_topc(C_487,D_490)
      | ~ m1_subset_1(E_491,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_488),u1_struct_0(B_489))))
      | ~ v1_funct_2(E_491,u1_struct_0(A_488),u1_struct_0(B_489))
      | ~ v1_funct_1(E_491)
      | ~ m1_pre_topc(D_490,A_488)
      | v2_struct_0(D_490)
      | ~ m1_pre_topc(C_487,A_488)
      | v2_struct_0(C_487)
      | ~ l1_pre_topc(B_489)
      | ~ v2_pre_topc(B_489)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_1856,plain,
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
    inference(resolution,[status(thm)],[c_1430,c_1852])).

tff(c_1863,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_52,c_50,c_40,c_38,c_36,c_34,c_516,c_513,c_510,c_1856])).

tff(c_1864,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_48,c_44,c_1863])).

tff(c_2011,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_2014,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_348,c_2011])).

tff(c_2017,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_2014])).

tff(c_2019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2017])).

tff(c_2020,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_2225,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2020])).

tff(c_2228,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_340,c_2225])).

tff(c_2231,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_2228])).

tff(c_2233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2231])).

tff(c_2234,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2020])).

tff(c_419,plain,(
    ! [C_396,G_397,B_399,E_400,D_401,A_398] :
      ( r1_tmap_1(D_401,B_399,k3_tmap_1(A_398,B_399,C_396,D_401,E_400),G_397)
      | ~ r1_tmap_1(C_396,B_399,E_400,G_397)
      | ~ m1_pre_topc(D_401,C_396)
      | ~ m1_subset_1(G_397,u1_struct_0(D_401))
      | ~ m1_subset_1(G_397,u1_struct_0(C_396))
      | ~ m1_subset_1(E_400,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396),u1_struct_0(B_399))))
      | ~ v1_funct_2(E_400,u1_struct_0(C_396),u1_struct_0(B_399))
      | ~ v1_funct_1(E_400)
      | ~ m1_pre_topc(D_401,A_398)
      | v2_struct_0(D_401)
      | ~ m1_pre_topc(C_396,A_398)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc(B_399)
      | ~ v2_pre_topc(B_399)
      | v2_struct_0(B_399)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_1437,plain,(
    ! [C_476,E_480,A_478,D_479,B_474,D_477,G_475,A_473] :
      ( r1_tmap_1(D_479,B_474,k3_tmap_1(A_478,B_474,D_477,D_479,k3_tmap_1(A_473,B_474,C_476,D_477,E_480)),G_475)
      | ~ r1_tmap_1(D_477,B_474,k3_tmap_1(A_473,B_474,C_476,D_477,E_480),G_475)
      | ~ m1_pre_topc(D_479,D_477)
      | ~ m1_subset_1(G_475,u1_struct_0(D_479))
      | ~ m1_subset_1(G_475,u1_struct_0(D_477))
      | ~ v1_funct_2(k3_tmap_1(A_473,B_474,C_476,D_477,E_480),u1_struct_0(D_477),u1_struct_0(B_474))
      | ~ v1_funct_1(k3_tmap_1(A_473,B_474,C_476,D_477,E_480))
      | ~ m1_pre_topc(D_479,A_478)
      | v2_struct_0(D_479)
      | ~ m1_pre_topc(D_477,A_478)
      | v2_struct_0(D_477)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478)
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_476),u1_struct_0(B_474))))
      | ~ v1_funct_2(E_480,u1_struct_0(C_476),u1_struct_0(B_474))
      | ~ v1_funct_1(E_480)
      | ~ m1_pre_topc(D_477,A_473)
      | ~ m1_pre_topc(C_476,A_473)
      | ~ l1_pre_topc(B_474)
      | ~ v2_pre_topc(B_474)
      | v2_struct_0(B_474)
      | ~ l1_pre_topc(A_473)
      | ~ v2_pre_topc(A_473)
      | v2_struct_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_10,c_419])).

tff(c_1459,plain,(
    ! [A_372,A_478,D_479,D_375,G_475] :
      ( r1_tmap_1(D_479,'#skF_2',k3_tmap_1(A_478,'#skF_2',D_375,D_479,k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5')),G_475)
      | ~ r1_tmap_1(D_375,'#skF_2',k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'),G_475)
      | ~ m1_pre_topc(D_479,D_375)
      | ~ m1_subset_1(G_475,u1_struct_0(D_479))
      | ~ m1_subset_1(G_475,u1_struct_0(D_375))
      | ~ v1_funct_1(k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'))
      | ~ m1_pre_topc(D_479,A_478)
      | v2_struct_0(D_479)
      | ~ m1_pre_topc(D_375,A_478)
      | v2_struct_0(D_375)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc('#skF_1',A_372)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_188,c_1437])).

tff(c_1493,plain,(
    ! [A_372,A_478,D_479,D_375,G_475] :
      ( r1_tmap_1(D_479,'#skF_2',k3_tmap_1(A_478,'#skF_2',D_375,D_479,k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5')),G_475)
      | ~ r1_tmap_1(D_375,'#skF_2',k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'),G_475)
      | ~ m1_pre_topc(D_479,D_375)
      | ~ m1_subset_1(G_475,u1_struct_0(D_479))
      | ~ m1_subset_1(G_475,u1_struct_0(D_375))
      | ~ v1_funct_1(k3_tmap_1(A_372,'#skF_2','#skF_1',D_375,'#skF_5'))
      | ~ m1_pre_topc(D_479,A_478)
      | v2_struct_0(D_479)
      | ~ m1_pre_topc(D_375,A_478)
      | v2_struct_0(D_375)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_375,A_372)
      | ~ m1_pre_topc('#skF_1',A_372)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_36,c_1459])).

tff(c_3067,plain,(
    ! [A_517,D_516,G_513,D_515,A_514] :
      ( r1_tmap_1(D_516,'#skF_2',k3_tmap_1(A_517,'#skF_2',D_515,D_516,k3_tmap_1(A_514,'#skF_2','#skF_1',D_515,'#skF_5')),G_513)
      | ~ r1_tmap_1(D_515,'#skF_2',k3_tmap_1(A_514,'#skF_2','#skF_1',D_515,'#skF_5'),G_513)
      | ~ m1_pre_topc(D_516,D_515)
      | ~ m1_subset_1(G_513,u1_struct_0(D_516))
      | ~ m1_subset_1(G_513,u1_struct_0(D_515))
      | ~ v1_funct_1(k3_tmap_1(A_514,'#skF_2','#skF_1',D_515,'#skF_5'))
      | ~ m1_pre_topc(D_516,A_517)
      | v2_struct_0(D_516)
      | ~ m1_pre_topc(D_515,A_517)
      | v2_struct_0(D_515)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517)
      | ~ m1_pre_topc(D_515,A_514)
      | ~ m1_pre_topc('#skF_1',A_514)
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1493])).

tff(c_3082,plain,(
    ! [D_516,A_517,G_513] :
      ( r1_tmap_1(D_516,'#skF_2',k3_tmap_1(A_517,'#skF_2','#skF_4',D_516,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),G_513)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),G_513)
      | ~ m1_pre_topc(D_516,'#skF_4')
      | ~ m1_subset_1(G_513,u1_struct_0(D_516))
      | ~ m1_subset_1(G_513,u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_516,A_517)
      | v2_struct_0(D_516)
      | ~ m1_pre_topc('#skF_4',A_517)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_3067])).

tff(c_3090,plain,(
    ! [D_516,A_517,G_513] :
      ( r1_tmap_1(D_516,'#skF_2',k3_tmap_1(A_517,'#skF_2','#skF_4',D_516,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),G_513)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_513)
      | ~ m1_pre_topc(D_516,'#skF_4')
      | ~ m1_subset_1(G_513,u1_struct_0(D_516))
      | ~ m1_subset_1(G_513,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_516,A_517)
      | v2_struct_0(D_516)
      | ~ m1_pre_topc('#skF_4',A_517)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_255,c_42,c_316,c_291,c_291,c_3082])).

tff(c_3804,plain,(
    ! [D_557,A_558,G_559] :
      ( r1_tmap_1(D_557,'#skF_2',k3_tmap_1(A_558,'#skF_2','#skF_4',D_557,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),G_559)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_559)
      | ~ m1_pre_topc(D_557,'#skF_4')
      | ~ m1_subset_1(G_559,u1_struct_0(D_557))
      | ~ m1_subset_1(G_559,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_557,A_558)
      | v2_struct_0(D_557)
      | ~ m1_pre_topc('#skF_4',A_558)
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558)
      | v2_struct_0(A_558) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_3090])).

tff(c_3807,plain,(
    ! [G_559] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_559)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_559)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1(G_559,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_559,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_3804])).

tff(c_3812,plain,(
    ! [G_559] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_559)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_559)
      | ~ m1_subset_1(G_559,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_559,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_46,c_34,c_3807])).

tff(c_3818,plain,(
    ! [G_561] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),G_561)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),G_561)
      | ~ m1_subset_1(G_561,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_561,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_48,c_3812])).

tff(c_24,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_281])).

tff(c_62,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24])).

tff(c_3821,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3818,c_62])).

tff(c_3825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_61,c_26,c_3821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.25/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.47  
% 7.25/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.47  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.25/2.47  
% 7.25/2.47  %Foreground sorts:
% 7.25/2.47  
% 7.25/2.47  
% 7.25/2.47  %Background operators:
% 7.25/2.47  
% 7.25/2.47  
% 7.25/2.47  %Foreground operators:
% 7.25/2.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.25/2.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.25/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.25/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.25/2.47  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.25/2.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.25/2.47  tff('#skF_7', type, '#skF_7': $i).
% 7.25/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.25/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.25/2.47  tff('#skF_6', type, '#skF_6': $i).
% 7.25/2.47  tff('#skF_2', type, '#skF_2': $i).
% 7.25/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.25/2.47  tff('#skF_1', type, '#skF_1': $i).
% 7.25/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.25/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.25/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.25/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.25/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.25/2.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.25/2.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.25/2.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.25/2.47  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.25/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.25/2.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.25/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.25/2.47  
% 7.56/2.50  tff(f_281, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 7.56/2.50  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.56/2.50  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 7.56/2.50  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.56/2.50  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.56/2.50  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 7.56/2.50  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.56/2.50  tff(f_232, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 7.56/2.50  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_28, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_61, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 7.56/2.50  tff(c_26, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_16, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.56/2.50  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_203, plain, (![A_386, D_385, B_387, C_388, E_384]: (k3_tmap_1(A_386, B_387, C_388, D_385, E_384)=k2_partfun1(u1_struct_0(C_388), u1_struct_0(B_387), E_384, u1_struct_0(D_385)) | ~m1_pre_topc(D_385, C_388) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_388), u1_struct_0(B_387)))) | ~v1_funct_2(E_384, u1_struct_0(C_388), u1_struct_0(B_387)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_385, A_386) | ~m1_pre_topc(C_388, A_386) | ~l1_pre_topc(B_387) | ~v2_pre_topc(B_387) | v2_struct_0(B_387) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.56/2.50  tff(c_207, plain, (![A_386, D_385]: (k3_tmap_1(A_386, '#skF_2', '#skF_1', D_385, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_385)) | ~m1_pre_topc(D_385, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_385, A_386) | ~m1_pre_topc('#skF_1', A_386) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(resolution, [status(thm)], [c_36, c_203])).
% 7.56/2.50  tff(c_211, plain, (![A_386, D_385]: (k3_tmap_1(A_386, '#skF_2', '#skF_1', D_385, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_385)) | ~m1_pre_topc(D_385, '#skF_1') | ~m1_pre_topc(D_385, A_386) | ~m1_pre_topc('#skF_1', A_386) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_207])).
% 7.56/2.50  tff(c_213, plain, (![A_389, D_390]: (k3_tmap_1(A_389, '#skF_2', '#skF_1', D_390, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_390)) | ~m1_pre_topc(D_390, '#skF_1') | ~m1_pre_topc(D_390, A_389) | ~m1_pre_topc('#skF_1', A_389) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389))), inference(negUnitSimplification, [status(thm)], [c_54, c_211])).
% 7.56/2.50  tff(c_221, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_213])).
% 7.56/2.50  tff(c_235, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_221])).
% 7.56/2.50  tff(c_236, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_235])).
% 7.56/2.50  tff(c_245, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_236])).
% 7.56/2.50  tff(c_249, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_245])).
% 7.56/2.50  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_249])).
% 7.56/2.50  tff(c_255, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_236])).
% 7.56/2.50  tff(c_254, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_236])).
% 7.56/2.50  tff(c_166, plain, (![A_367, B_368, C_369, D_370]: (k2_partfun1(u1_struct_0(A_367), u1_struct_0(B_368), C_369, u1_struct_0(D_370))=k2_tmap_1(A_367, B_368, C_369, D_370) | ~m1_pre_topc(D_370, A_367) | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_367), u1_struct_0(B_368)))) | ~v1_funct_2(C_369, u1_struct_0(A_367), u1_struct_0(B_368)) | ~v1_funct_1(C_369) | ~l1_pre_topc(B_368) | ~v2_pre_topc(B_368) | v2_struct_0(B_368) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.56/2.50  tff(c_168, plain, (![D_370]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_370))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_370) | ~m1_pre_topc(D_370, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_166])).
% 7.56/2.50  tff(c_171, plain, (![D_370]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_370))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_370) | ~m1_pre_topc(D_370, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_40, c_38, c_168])).
% 7.56/2.50  tff(c_172, plain, (![D_370]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_370))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_370) | ~m1_pre_topc(D_370, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_171])).
% 7.56/2.50  tff(c_284, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_172])).
% 7.56/2.50  tff(c_291, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_284])).
% 7.56/2.50  tff(c_158, plain, (![E_364, B_361, D_363, C_362, A_360]: (v1_funct_1(k3_tmap_1(A_360, B_361, C_362, D_363, E_364)) | ~m1_subset_1(E_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_362), u1_struct_0(B_361)))) | ~v1_funct_2(E_364, u1_struct_0(C_362), u1_struct_0(B_361)) | ~v1_funct_1(E_364) | ~m1_pre_topc(D_363, A_360) | ~m1_pre_topc(C_362, A_360) | ~l1_pre_topc(B_361) | ~v2_pre_topc(B_361) | v2_struct_0(B_361) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.50  tff(c_160, plain, (![A_360, D_363]: (v1_funct_1(k3_tmap_1(A_360, '#skF_2', '#skF_1', D_363, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_363, A_360) | ~m1_pre_topc('#skF_1', A_360) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(resolution, [status(thm)], [c_36, c_158])).
% 7.56/2.50  tff(c_163, plain, (![A_360, D_363]: (v1_funct_1(k3_tmap_1(A_360, '#skF_2', '#skF_1', D_363, '#skF_5')) | ~m1_pre_topc(D_363, A_360) | ~m1_pre_topc('#skF_1', A_360) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_160])).
% 7.56/2.50  tff(c_164, plain, (![A_360, D_363]: (v1_funct_1(k3_tmap_1(A_360, '#skF_2', '#skF_1', D_363, '#skF_5')) | ~m1_pre_topc(D_363, A_360) | ~m1_pre_topc('#skF_1', A_360) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 7.56/2.50  tff(c_305, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_164])).
% 7.56/2.50  tff(c_315, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_42, c_305])).
% 7.56/2.50  tff(c_316, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_315])).
% 7.56/2.50  tff(c_182, plain, (![A_372, E_376, D_375, C_374, B_373]: (v1_funct_2(k3_tmap_1(A_372, B_373, C_374, D_375, E_376), u1_struct_0(D_375), u1_struct_0(B_373)) | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_374), u1_struct_0(B_373)))) | ~v1_funct_2(E_376, u1_struct_0(C_374), u1_struct_0(B_373)) | ~v1_funct_1(E_376) | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc(C_374, A_372) | ~l1_pre_topc(B_373) | ~v2_pre_topc(B_373) | v2_struct_0(B_373) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.50  tff(c_184, plain, (![A_372, D_375]: (v1_funct_2(k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5'), u1_struct_0(D_375), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc('#skF_1', A_372) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(resolution, [status(thm)], [c_36, c_182])).
% 7.56/2.50  tff(c_187, plain, (![A_372, D_375]: (v1_funct_2(k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5'), u1_struct_0(D_375), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc('#skF_1', A_372) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_184])).
% 7.56/2.50  tff(c_188, plain, (![A_372, D_375]: (v1_funct_2(k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5'), u1_struct_0(D_375), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc('#skF_1', A_372) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(negUnitSimplification, [status(thm)], [c_54, c_187])).
% 7.56/2.50  tff(c_302, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_188])).
% 7.56/2.50  tff(c_312, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_42, c_302])).
% 7.56/2.50  tff(c_313, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_312])).
% 7.56/2.50  tff(c_10, plain, (![B_52, E_55, C_53, D_54, A_51]: (m1_subset_1(k3_tmap_1(A_51, B_52, C_53, D_54, E_55), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_54), u1_struct_0(B_52)))) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.50  tff(c_299, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_10])).
% 7.56/2.50  tff(c_309, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_42, c_40, c_38, c_36, c_299])).
% 7.56/2.50  tff(c_310, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_309])).
% 7.56/2.50  tff(c_12, plain, (![B_52, E_55, C_53, D_54, A_51]: (v1_funct_2(k3_tmap_1(A_51, B_52, C_53, D_54, E_55), u1_struct_0(D_54), u1_struct_0(B_52)) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.50  tff(c_326, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_310, c_12])).
% 7.56/2.50  tff(c_339, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_326])).
% 7.56/2.50  tff(c_340, plain, (![A_51, D_54]: (v1_funct_2(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_54), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(negUnitSimplification, [status(thm)], [c_54, c_339])).
% 7.56/2.50  tff(c_14, plain, (![B_52, E_55, C_53, D_54, A_51]: (v1_funct_1(k3_tmap_1(A_51, B_52, C_53, D_54, E_55)) | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0(B_52)))) | ~v1_funct_2(E_55, u1_struct_0(C_53), u1_struct_0(B_52)) | ~v1_funct_1(E_55) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc(C_53, A_51) | ~l1_pre_topc(B_52) | ~v2_pre_topc(B_52) | v2_struct_0(B_52) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.50  tff(c_330, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_310, c_14])).
% 7.56/2.50  tff(c_347, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_330])).
% 7.56/2.50  tff(c_348, plain, (![A_51, D_54]: (v1_funct_1(k3_tmap_1(A_51, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_54, A_51) | ~m1_pre_topc('#skF_4', A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(negUnitSimplification, [status(thm)], [c_54, c_347])).
% 7.56/2.50  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_223, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_213])).
% 7.56/2.50  tff(c_239, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_223])).
% 7.56/2.50  tff(c_240, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_239])).
% 7.56/2.50  tff(c_480, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_240])).
% 7.56/2.50  tff(c_484, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_480, c_172])).
% 7.56/2.50  tff(c_491, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_484])).
% 7.56/2.50  tff(c_505, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_491, c_164])).
% 7.56/2.50  tff(c_515, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_46, c_505])).
% 7.56/2.50  tff(c_516, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_515])).
% 7.56/2.50  tff(c_502, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_491, c_188])).
% 7.56/2.50  tff(c_512, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_46, c_502])).
% 7.56/2.50  tff(c_513, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_512])).
% 7.56/2.50  tff(c_499, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_491, c_10])).
% 7.56/2.50  tff(c_509, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_255, c_46, c_40, c_38, c_36, c_499])).
% 7.56/2.50  tff(c_510, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_509])).
% 7.56/2.50  tff(c_8, plain, (![E_50, D_48, B_36, A_20, C_44]: (k3_tmap_1(A_20, B_36, C_44, D_48, E_50)=k2_partfun1(u1_struct_0(C_44), u1_struct_0(B_36), E_50, u1_struct_0(D_48)) | ~m1_pre_topc(D_48, C_44) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_44), u1_struct_0(B_36)))) | ~v1_funct_2(E_50, u1_struct_0(C_44), u1_struct_0(B_36)) | ~v1_funct_1(E_50) | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc(C_44, A_20) | ~l1_pre_topc(B_36) | ~v2_pre_topc(B_36) | v2_struct_0(B_36) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.56/2.50  tff(c_324, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(resolution, [status(thm)], [c_310, c_8])).
% 7.56/2.50  tff(c_335, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_324])).
% 7.56/2.50  tff(c_336, plain, (![A_20, D_48]: (k3_tmap_1(A_20, '#skF_2', '#skF_4', D_48, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_48)) | ~m1_pre_topc(D_48, '#skF_4') | ~m1_pre_topc(D_48, A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(negUnitSimplification, [status(thm)], [c_54, c_335])).
% 7.56/2.50  tff(c_1293, plain, (![A_469, D_470]: (k3_tmap_1(A_469, '#skF_2', '#skF_4', D_470, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_470)) | ~m1_pre_topc(D_470, '#skF_4') | ~m1_pre_topc(D_470, A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(negUnitSimplification, [status(thm)], [c_54, c_335])).
% 7.56/2.50  tff(c_1319, plain, (![D_470, A_469]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_470)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_470), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_470, A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469) | ~m1_pre_topc(D_470, '#skF_4') | ~m1_pre_topc(D_470, A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(superposition, [status(thm), theory('equality')], [c_1293, c_10])).
% 7.56/2.50  tff(c_1340, plain, (![D_470, A_469]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_470)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_470), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_470, '#skF_4') | ~m1_pre_topc(D_470, A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_316, c_313, c_310, c_1319])).
% 7.56/2.50  tff(c_1343, plain, (![D_471, A_472]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_471)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_471), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_471, '#skF_4') | ~m1_pre_topc(D_471, A_472) | ~m1_pre_topc('#skF_4', A_472) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(negUnitSimplification, [status(thm)], [c_54, c_1340])).
% 7.56/2.50  tff(c_1355, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1343])).
% 7.56/2.50  tff(c_1375, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_34, c_1355])).
% 7.56/2.50  tff(c_1376, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1375])).
% 7.56/2.50  tff(c_1399, plain, (![A_20]: (m1_subset_1(k3_tmap_1(A_20, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(superposition, [status(thm), theory('equality')], [c_336, c_1376])).
% 7.56/2.50  tff(c_1430, plain, (![A_20]: (m1_subset_1(k3_tmap_1(A_20, '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', A_20) | ~m1_pre_topc('#skF_4', A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1399])).
% 7.56/2.50  tff(c_318, plain, (![D_392, C_393, A_395, E_394, B_391]: (r2_funct_2(u1_struct_0(C_393), u1_struct_0(B_391), k3_tmap_1(A_395, B_391, D_392, C_393, k2_tmap_1(A_395, B_391, E_394, D_392)), k2_tmap_1(A_395, B_391, E_394, C_393)) | ~m1_pre_topc(C_393, D_392) | ~m1_subset_1(E_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0(B_391)))) | ~v1_funct_2(E_394, u1_struct_0(A_395), u1_struct_0(B_391)) | ~v1_funct_1(E_394) | ~m1_pre_topc(D_392, A_395) | v2_struct_0(D_392) | ~m1_pre_topc(C_393, A_395) | v2_struct_0(C_393) | ~l1_pre_topc(B_391) | ~v2_pre_topc(B_391) | v2_struct_0(B_391) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.56/2.50  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.56/2.50  tff(c_1852, plain, (![C_487, D_490, B_489, E_491, A_488]: (k3_tmap_1(A_488, B_489, D_490, C_487, k2_tmap_1(A_488, B_489, E_491, D_490))=k2_tmap_1(A_488, B_489, E_491, C_487) | ~m1_subset_1(k2_tmap_1(A_488, B_489, E_491, C_487), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_487), u1_struct_0(B_489)))) | ~v1_funct_2(k2_tmap_1(A_488, B_489, E_491, C_487), u1_struct_0(C_487), u1_struct_0(B_489)) | ~v1_funct_1(k2_tmap_1(A_488, B_489, E_491, C_487)) | ~m1_subset_1(k3_tmap_1(A_488, B_489, D_490, C_487, k2_tmap_1(A_488, B_489, E_491, D_490)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_487), u1_struct_0(B_489)))) | ~v1_funct_2(k3_tmap_1(A_488, B_489, D_490, C_487, k2_tmap_1(A_488, B_489, E_491, D_490)), u1_struct_0(C_487), u1_struct_0(B_489)) | ~v1_funct_1(k3_tmap_1(A_488, B_489, D_490, C_487, k2_tmap_1(A_488, B_489, E_491, D_490))) | ~m1_pre_topc(C_487, D_490) | ~m1_subset_1(E_491, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_488), u1_struct_0(B_489)))) | ~v1_funct_2(E_491, u1_struct_0(A_488), u1_struct_0(B_489)) | ~v1_funct_1(E_491) | ~m1_pre_topc(D_490, A_488) | v2_struct_0(D_490) | ~m1_pre_topc(C_487, A_488) | v2_struct_0(C_487) | ~l1_pre_topc(B_489) | ~v2_pre_topc(B_489) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488))), inference(resolution, [status(thm)], [c_318, c_4])).
% 7.56/2.50  tff(c_1856, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1430, c_1852])).
% 7.56/2.50  tff(c_1863, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_52, c_50, c_40, c_38, c_36, c_34, c_516, c_513, c_510, c_1856])).
% 7.56/2.50  tff(c_1864, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_48, c_44, c_1863])).
% 7.56/2.50  tff(c_2011, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1864])).
% 7.56/2.50  tff(c_2014, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_348, c_2011])).
% 7.56/2.50  tff(c_2017, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_2014])).
% 7.56/2.50  tff(c_2019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2017])).
% 7.56/2.50  tff(c_2020, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1864])).
% 7.56/2.50  tff(c_2225, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2020])).
% 7.56/2.50  tff(c_2228, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_340, c_2225])).
% 7.56/2.50  tff(c_2231, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_2228])).
% 7.56/2.50  tff(c_2233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2231])).
% 7.56/2.50  tff(c_2234, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_2020])).
% 7.56/2.50  tff(c_419, plain, (![C_396, G_397, B_399, E_400, D_401, A_398]: (r1_tmap_1(D_401, B_399, k3_tmap_1(A_398, B_399, C_396, D_401, E_400), G_397) | ~r1_tmap_1(C_396, B_399, E_400, G_397) | ~m1_pre_topc(D_401, C_396) | ~m1_subset_1(G_397, u1_struct_0(D_401)) | ~m1_subset_1(G_397, u1_struct_0(C_396)) | ~m1_subset_1(E_400, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396), u1_struct_0(B_399)))) | ~v1_funct_2(E_400, u1_struct_0(C_396), u1_struct_0(B_399)) | ~v1_funct_1(E_400) | ~m1_pre_topc(D_401, A_398) | v2_struct_0(D_401) | ~m1_pre_topc(C_396, A_398) | v2_struct_0(C_396) | ~l1_pre_topc(B_399) | ~v2_pre_topc(B_399) | v2_struct_0(B_399) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(cnfTransformation, [status(thm)], [f_232])).
% 7.56/2.50  tff(c_1437, plain, (![C_476, E_480, A_478, D_479, B_474, D_477, G_475, A_473]: (r1_tmap_1(D_479, B_474, k3_tmap_1(A_478, B_474, D_477, D_479, k3_tmap_1(A_473, B_474, C_476, D_477, E_480)), G_475) | ~r1_tmap_1(D_477, B_474, k3_tmap_1(A_473, B_474, C_476, D_477, E_480), G_475) | ~m1_pre_topc(D_479, D_477) | ~m1_subset_1(G_475, u1_struct_0(D_479)) | ~m1_subset_1(G_475, u1_struct_0(D_477)) | ~v1_funct_2(k3_tmap_1(A_473, B_474, C_476, D_477, E_480), u1_struct_0(D_477), u1_struct_0(B_474)) | ~v1_funct_1(k3_tmap_1(A_473, B_474, C_476, D_477, E_480)) | ~m1_pre_topc(D_479, A_478) | v2_struct_0(D_479) | ~m1_pre_topc(D_477, A_478) | v2_struct_0(D_477) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_476), u1_struct_0(B_474)))) | ~v1_funct_2(E_480, u1_struct_0(C_476), u1_struct_0(B_474)) | ~v1_funct_1(E_480) | ~m1_pre_topc(D_477, A_473) | ~m1_pre_topc(C_476, A_473) | ~l1_pre_topc(B_474) | ~v2_pre_topc(B_474) | v2_struct_0(B_474) | ~l1_pre_topc(A_473) | ~v2_pre_topc(A_473) | v2_struct_0(A_473))), inference(resolution, [status(thm)], [c_10, c_419])).
% 7.56/2.50  tff(c_1459, plain, (![A_372, A_478, D_479, D_375, G_475]: (r1_tmap_1(D_479, '#skF_2', k3_tmap_1(A_478, '#skF_2', D_375, D_479, k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5')), G_475) | ~r1_tmap_1(D_375, '#skF_2', k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5'), G_475) | ~m1_pre_topc(D_479, D_375) | ~m1_subset_1(G_475, u1_struct_0(D_479)) | ~m1_subset_1(G_475, u1_struct_0(D_375)) | ~v1_funct_1(k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5')) | ~m1_pre_topc(D_479, A_478) | v2_struct_0(D_479) | ~m1_pre_topc(D_375, A_478) | v2_struct_0(D_375) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc('#skF_1', A_372) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(resolution, [status(thm)], [c_188, c_1437])).
% 7.56/2.50  tff(c_1493, plain, (![A_372, A_478, D_479, D_375, G_475]: (r1_tmap_1(D_479, '#skF_2', k3_tmap_1(A_478, '#skF_2', D_375, D_479, k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5')), G_475) | ~r1_tmap_1(D_375, '#skF_2', k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5'), G_475) | ~m1_pre_topc(D_479, D_375) | ~m1_subset_1(G_475, u1_struct_0(D_479)) | ~m1_subset_1(G_475, u1_struct_0(D_375)) | ~v1_funct_1(k3_tmap_1(A_372, '#skF_2', '#skF_1', D_375, '#skF_5')) | ~m1_pre_topc(D_479, A_478) | v2_struct_0(D_479) | ~m1_pre_topc(D_375, A_478) | v2_struct_0(D_375) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_375, A_372) | ~m1_pre_topc('#skF_1', A_372) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_36, c_1459])).
% 7.56/2.50  tff(c_3067, plain, (![A_517, D_516, G_513, D_515, A_514]: (r1_tmap_1(D_516, '#skF_2', k3_tmap_1(A_517, '#skF_2', D_515, D_516, k3_tmap_1(A_514, '#skF_2', '#skF_1', D_515, '#skF_5')), G_513) | ~r1_tmap_1(D_515, '#skF_2', k3_tmap_1(A_514, '#skF_2', '#skF_1', D_515, '#skF_5'), G_513) | ~m1_pre_topc(D_516, D_515) | ~m1_subset_1(G_513, u1_struct_0(D_516)) | ~m1_subset_1(G_513, u1_struct_0(D_515)) | ~v1_funct_1(k3_tmap_1(A_514, '#skF_2', '#skF_1', D_515, '#skF_5')) | ~m1_pre_topc(D_516, A_517) | v2_struct_0(D_516) | ~m1_pre_topc(D_515, A_517) | v2_struct_0(D_515) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517) | ~m1_pre_topc(D_515, A_514) | ~m1_pre_topc('#skF_1', A_514) | ~l1_pre_topc(A_514) | ~v2_pre_topc(A_514) | v2_struct_0(A_514))), inference(negUnitSimplification, [status(thm)], [c_54, c_1493])).
% 7.56/2.50  tff(c_3082, plain, (![D_516, A_517, G_513]: (r1_tmap_1(D_516, '#skF_2', k3_tmap_1(A_517, '#skF_2', '#skF_4', D_516, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), G_513) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), G_513) | ~m1_pre_topc(D_516, '#skF_4') | ~m1_subset_1(G_513, u1_struct_0(D_516)) | ~m1_subset_1(G_513, u1_struct_0('#skF_4')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_516, A_517) | v2_struct_0(D_516) | ~m1_pre_topc('#skF_4', A_517) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_3067])).
% 7.56/2.50  tff(c_3090, plain, (![D_516, A_517, G_513]: (r1_tmap_1(D_516, '#skF_2', k3_tmap_1(A_517, '#skF_2', '#skF_4', D_516, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), G_513) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_513) | ~m1_pre_topc(D_516, '#skF_4') | ~m1_subset_1(G_513, u1_struct_0(D_516)) | ~m1_subset_1(G_513, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_516, A_517) | v2_struct_0(D_516) | ~m1_pre_topc('#skF_4', A_517) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_255, c_42, c_316, c_291, c_291, c_3082])).
% 7.56/2.50  tff(c_3804, plain, (![D_557, A_558, G_559]: (r1_tmap_1(D_557, '#skF_2', k3_tmap_1(A_558, '#skF_2', '#skF_4', D_557, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), G_559) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_559) | ~m1_pre_topc(D_557, '#skF_4') | ~m1_subset_1(G_559, u1_struct_0(D_557)) | ~m1_subset_1(G_559, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_557, A_558) | v2_struct_0(D_557) | ~m1_pre_topc('#skF_4', A_558) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558) | v2_struct_0(A_558))), inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_3090])).
% 7.56/2.50  tff(c_3807, plain, (![G_559]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_559) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_559) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(G_559, u1_struct_0('#skF_3')) | ~m1_subset_1(G_559, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2234, c_3804])).
% 7.56/2.50  tff(c_3812, plain, (![G_559]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_559) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_559) | ~m1_subset_1(G_559, u1_struct_0('#skF_3')) | ~m1_subset_1(G_559, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_46, c_34, c_3807])).
% 7.56/2.50  tff(c_3818, plain, (![G_561]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), G_561) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), G_561) | ~m1_subset_1(G_561, u1_struct_0('#skF_3')) | ~m1_subset_1(G_561, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_48, c_3812])).
% 7.56/2.50  tff(c_24, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_281])).
% 7.56/2.50  tff(c_62, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24])).
% 7.56/2.50  tff(c_3821, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3818, c_62])).
% 7.56/2.50  tff(c_3825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_61, c_26, c_3821])).
% 7.56/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.50  
% 7.56/2.50  Inference rules
% 7.56/2.50  ----------------------
% 7.56/2.50  #Ref     : 0
% 7.56/2.50  #Sup     : 696
% 7.56/2.50  #Fact    : 0
% 7.56/2.50  #Define  : 0
% 7.56/2.50  #Split   : 18
% 7.56/2.50  #Chain   : 0
% 7.56/2.50  #Close   : 0
% 7.56/2.50  
% 7.56/2.50  Ordering : KBO
% 7.56/2.50  
% 7.56/2.50  Simplification rules
% 7.56/2.50  ----------------------
% 7.56/2.50  #Subsume      : 116
% 7.56/2.50  #Demod        : 2505
% 7.56/2.50  #Tautology    : 190
% 7.56/2.50  #SimpNegUnit  : 457
% 7.56/2.50  #BackRed      : 10
% 7.56/2.50  
% 7.56/2.50  #Partial instantiations: 0
% 7.56/2.50  #Strategies tried      : 1
% 7.56/2.50  
% 7.56/2.50  Timing (in seconds)
% 7.56/2.50  ----------------------
% 7.56/2.50  Preprocessing        : 0.39
% 7.56/2.50  Parsing              : 0.20
% 7.56/2.50  CNF conversion       : 0.05
% 7.56/2.50  Main loop            : 1.30
% 7.56/2.50  Inferencing          : 0.40
% 7.56/2.50  Reduction            : 0.51
% 7.56/2.50  Demodulation         : 0.39
% 7.56/2.50  BG Simplification    : 0.05
% 7.56/2.50  Subsumption          : 0.29
% 7.56/2.51  Abstraction          : 0.08
% 7.56/2.51  MUC search           : 0.00
% 7.56/2.51  Cooper               : 0.00
% 7.56/2.51  Total                : 1.75
% 7.68/2.51  Index Insertion      : 0.00
% 7.68/2.51  Index Deletion       : 0.00
% 7.68/2.51  Index Matching       : 0.00
% 7.68/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
