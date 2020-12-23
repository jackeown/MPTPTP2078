%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:17 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  123 (1685 expanded)
%              Number of leaves         :   31 ( 684 expanded)
%              Depth                    :   22
%              Number of atoms          :  490 (13882 expanded)
%              Number of equality atoms :   30 ( 257 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_227,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(D,C)
                            & m1_pre_topc(E,D) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_180,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_28,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_86,plain,(
    ! [B_155,A_156] :
      ( v2_pre_topc(B_155)
      | ~ m1_pre_topc(B_155,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_86])).

tff(c_110,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_95])).

tff(c_55,plain,(
    ! [B_153,A_154] :
      ( l1_pre_topc(B_153)
      | ~ m1_pre_topc(B_153,A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_77,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_117,plain,(
    ! [C_157,A_158,B_159] :
      ( m1_pre_topc(C_157,A_158)
      | ~ m1_pre_topc(C_157,B_159)
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_131,plain,(
    ! [A_158] :
      ( m1_pre_topc('#skF_5',A_158)
      | ~ m1_pre_topc('#skF_4',A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_32,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_24,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_359,plain,(
    ! [E_198,C_199,D_195,B_197,A_196] :
      ( k3_tmap_1(A_196,B_197,C_199,D_195,E_198) = k2_partfun1(u1_struct_0(C_199),u1_struct_0(B_197),E_198,u1_struct_0(D_195))
      | ~ m1_pre_topc(D_195,C_199)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199),u1_struct_0(B_197))))
      | ~ v1_funct_2(E_198,u1_struct_0(C_199),u1_struct_0(B_197))
      | ~ v1_funct_1(E_198)
      | ~ m1_pre_topc(D_195,A_196)
      | ~ m1_pre_topc(C_199,A_196)
      | ~ l1_pre_topc(B_197)
      | ~ v2_pre_topc(B_197)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_363,plain,(
    ! [A_196,D_195] :
      ( k3_tmap_1(A_196,'#skF_2','#skF_3',D_195,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_195))
      | ~ m1_pre_topc(D_195,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_195,A_196)
      | ~ m1_pre_topc('#skF_3',A_196)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_22,c_359])).

tff(c_367,plain,(
    ! [A_196,D_195] :
      ( k3_tmap_1(A_196,'#skF_2','#skF_3',D_195,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_195))
      | ~ m1_pre_topc(D_195,'#skF_3')
      | ~ m1_pre_topc(D_195,A_196)
      | ~ m1_pre_topc('#skF_3',A_196)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_26,c_24,c_363])).

tff(c_370,plain,(
    ! [A_205,D_206] :
      ( k3_tmap_1(A_205,'#skF_2','#skF_3',D_206,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_206))
      | ~ m1_pre_topc(D_206,'#skF_3')
      | ~ m1_pre_topc(D_206,A_205)
      | ~ m1_pre_topc('#skF_3',A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_367])).

tff(c_386,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_370])).

tff(c_408,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_386])).

tff(c_409,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_408])).

tff(c_489,plain,(
    ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_507,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_489])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_77,c_30,c_507])).

tff(c_516,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_89,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_104,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_89])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_73,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_378,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_392,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_30,c_378])).

tff(c_393,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_392])).

tff(c_283,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k2_partfun1(u1_struct_0(A_176),u1_struct_0(B_177),C_178,u1_struct_0(D_179)) = k2_tmap_1(A_176,B_177,C_178,D_179)
      | ~ m1_pre_topc(D_179,A_176)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(B_177))))
      | ~ v1_funct_2(C_178,u1_struct_0(A_176),u1_struct_0(B_177))
      | ~ v1_funct_1(C_178)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_285,plain,(
    ! [D_179] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_179)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_179)
      | ~ m1_pre_topc(D_179,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_283])).

tff(c_288,plain,(
    ! [D_179] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_179)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_179)
      | ~ m1_pre_topc(D_179,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_77,c_46,c_44,c_26,c_24,c_285])).

tff(c_289,plain,(
    ! [D_179] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_179)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_179)
      | ~ m1_pre_topc(D_179,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48,c_288])).

tff(c_413,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_289])).

tff(c_420,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_413])).

tff(c_177,plain,(
    ! [E_166,A_165,D_167,B_168,C_164] :
      ( v1_funct_1(k3_tmap_1(A_165,B_168,C_164,D_167,E_166))
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_164),u1_struct_0(B_168))))
      | ~ v1_funct_2(E_166,u1_struct_0(C_164),u1_struct_0(B_168))
      | ~ v1_funct_1(E_166)
      | ~ m1_pre_topc(D_167,A_165)
      | ~ m1_pre_topc(C_164,A_165)
      | ~ l1_pre_topc(B_168)
      | ~ v2_pre_topc(B_168)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_179,plain,(
    ! [A_165,D_167] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_3',D_167,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_167,A_165)
      | ~ m1_pre_topc('#skF_3',A_165)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_22,c_177])).

tff(c_182,plain,(
    ! [A_165,D_167] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_3',D_167,'#skF_6'))
      | ~ m1_pre_topc(D_167,A_165)
      | ~ m1_pre_topc('#skF_3',A_165)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_26,c_24,c_179])).

tff(c_183,plain,(
    ! [A_165,D_167] :
      ( v1_funct_1(k3_tmap_1(A_165,'#skF_2','#skF_3',D_167,'#skF_6'))
      | ~ m1_pre_topc(D_167,A_165)
      | ~ m1_pre_topc('#skF_3',A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_182])).

tff(c_435,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_183])).

tff(c_445,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_435])).

tff(c_446,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_445])).

tff(c_341,plain,(
    ! [E_185,D_186,C_183,A_184,B_187] :
      ( v1_funct_2(k3_tmap_1(A_184,B_187,C_183,D_186,E_185),u1_struct_0(D_186),u1_struct_0(B_187))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183),u1_struct_0(B_187))))
      | ~ v1_funct_2(E_185,u1_struct_0(C_183),u1_struct_0(B_187))
      | ~ v1_funct_1(E_185)
      | ~ m1_pre_topc(D_186,A_184)
      | ~ m1_pre_topc(C_183,A_184)
      | ~ l1_pre_topc(B_187)
      | ~ v2_pre_topc(B_187)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_343,plain,(
    ! [A_184,D_186] :
      ( v1_funct_2(k3_tmap_1(A_184,'#skF_2','#skF_3',D_186,'#skF_6'),u1_struct_0(D_186),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_186,A_184)
      | ~ m1_pre_topc('#skF_3',A_184)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_22,c_341])).

tff(c_346,plain,(
    ! [A_184,D_186] :
      ( v1_funct_2(k3_tmap_1(A_184,'#skF_2','#skF_3',D_186,'#skF_6'),u1_struct_0(D_186),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_186,A_184)
      | ~ m1_pre_topc('#skF_3',A_184)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_26,c_24,c_343])).

tff(c_347,plain,(
    ! [A_184,D_186] :
      ( v1_funct_2(k3_tmap_1(A_184,'#skF_2','#skF_3',D_186,'#skF_6'),u1_struct_0(D_186),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_186,A_184)
      | ~ m1_pre_topc('#skF_3',A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_346])).

tff(c_432,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_347])).

tff(c_442,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_36,c_432])).

tff(c_443,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_442])).

tff(c_10,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] :
      ( m1_subset_1(k3_tmap_1(A_53,B_54,C_55,D_56,E_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56),u1_struct_0(B_54))))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55),u1_struct_0(B_54))))
      | ~ v1_funct_2(E_57,u1_struct_0(C_55),u1_struct_0(B_54))
      | ~ v1_funct_1(E_57)
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc(C_55,A_53)
      | ~ l1_pre_topc(B_54)
      | ~ v2_pre_topc(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_429,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_10])).

tff(c_439,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_44,c_40,c_36,c_26,c_24,c_22,c_429])).

tff(c_440,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_439])).

tff(c_6,plain,(
    ! [A_7,B_15,C_19,D_21] :
      ( k2_partfun1(u1_struct_0(A_7),u1_struct_0(B_15),C_19,u1_struct_0(D_21)) = k2_tmap_1(A_7,B_15,C_19,D_21)
      | ~ m1_pre_topc(D_21,A_7)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(B_15))))
      | ~ v1_funct_2(C_19,u1_struct_0(A_7),u1_struct_0(B_15))
      | ~ v1_funct_1(C_19)
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_454,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_440,c_6])).

tff(c_467,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_73,c_46,c_44,c_446,c_443,c_454])).

tff(c_468,plain,(
    ! [D_21] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_21)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_21)
      | ~ m1_pre_topc(D_21,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_48,c_467])).

tff(c_8,plain,(
    ! [C_46,B_38,E_52,D_50,A_22] :
      ( k3_tmap_1(A_22,B_38,C_46,D_50,E_52) = k2_partfun1(u1_struct_0(C_46),u1_struct_0(B_38),E_52,u1_struct_0(D_50))
      | ~ m1_pre_topc(D_50,C_46)
      | ~ m1_subset_1(E_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_46),u1_struct_0(B_38))))
      | ~ v1_funct_2(E_52,u1_struct_0(C_46),u1_struct_0(B_38))
      | ~ v1_funct_1(E_52)
      | ~ m1_pre_topc(D_50,A_22)
      | ~ m1_pre_topc(C_46,A_22)
      | ~ l1_pre_topc(B_38)
      | ~ v2_pre_topc(B_38)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_450,plain,(
    ! [A_22,D_50] :
      ( k3_tmap_1(A_22,'#skF_2','#skF_4',D_50,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_50))
      | ~ m1_pre_topc(D_50,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'))
      | ~ m1_pre_topc(D_50,A_22)
      | ~ m1_pre_topc('#skF_4',A_22)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_440,c_8])).

tff(c_459,plain,(
    ! [A_22,D_50] :
      ( k3_tmap_1(A_22,'#skF_2','#skF_4',D_50,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_50))
      | ~ m1_pre_topc(D_50,'#skF_4')
      | ~ m1_pre_topc(D_50,A_22)
      | ~ m1_pre_topc('#skF_4',A_22)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_446,c_443,c_450])).

tff(c_844,plain,(
    ! [A_249,D_250] :
      ( k3_tmap_1(A_249,'#skF_2','#skF_4',D_250,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),u1_struct_0(D_250))
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ m1_pre_topc(D_250,A_249)
      | ~ m1_pre_topc('#skF_4',A_249)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_459])).

tff(c_1417,plain,(
    ! [A_285,D_286] :
      ( k3_tmap_1(A_285,'#skF_2','#skF_4',D_286,k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_286)
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_pre_topc(D_286,A_285)
      | ~ m1_pre_topc('#skF_4',A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ m1_pre_topc(D_286,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_844])).

tff(c_16,plain,(
    ! [A_58,E_88,B_74,D_86,C_82] :
      ( r2_funct_2(u1_struct_0(C_82),u1_struct_0(B_74),k3_tmap_1(A_58,B_74,D_86,C_82,k2_tmap_1(A_58,B_74,E_88,D_86)),k2_tmap_1(A_58,B_74,E_88,C_82))
      | ~ m1_pre_topc(C_82,D_86)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(B_74))))
      | ~ v1_funct_2(E_88,u1_struct_0(A_58),u1_struct_0(B_74))
      | ~ v1_funct_1(E_88)
      | ~ m1_pre_topc(D_86,A_58)
      | v2_struct_0(D_86)
      | ~ m1_pre_topc(C_82,A_58)
      | v2_struct_0(C_82)
      | ~ l1_pre_topc(B_74)
      | ~ v2_pre_topc(B_74)
      | v2_struct_0(B_74)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1448,plain,(
    ! [D_286] :
      ( r2_funct_2(u1_struct_0(D_286),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_286),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_286))
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_286,'#skF_3')
      | v2_struct_0(D_286)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_286,'#skF_4')
      | ~ m1_pre_topc(D_286,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_286,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_16])).

tff(c_1471,plain,(
    ! [D_286] :
      ( r2_funct_2(u1_struct_0(D_286),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_286),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_286))
      | v2_struct_0('#skF_4')
      | v2_struct_0(D_286)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_286,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_286,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_77,c_30,c_110,c_77,c_46,c_44,c_30,c_26,c_24,c_22,c_1448])).

tff(c_1477,plain,(
    ! [D_287] :
      ( r2_funct_2(u1_struct_0(D_287),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),D_287),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_287))
      | v2_struct_0(D_287)
      | ~ m1_pre_topc(D_287,'#skF_3')
      | ~ m1_pre_topc(D_287,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_48,c_38,c_1471])).

tff(c_515,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_597,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_289])).

tff(c_604,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_597])).

tff(c_20,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_425,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_20])).

tff(c_767,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_425])).

tff(c_1439,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_767])).

tff(c_1462,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52,c_50,c_36,c_32,c_28,c_1439])).

tff(c_1463,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1462])).

tff(c_1480,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1477,c_1463])).

tff(c_1483,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_516,c_1480])).

tff(c_1485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:57:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.83  
% 4.56/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.83  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.76/1.83  
% 4.76/1.83  %Foreground sorts:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Background operators:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Foreground operators:
% 4.76/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.76/1.83  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.76/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.76/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.76/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.76/1.83  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.76/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.76/1.83  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.76/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.76/1.83  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.76/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.83  
% 4.83/1.85  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tmap_1)).
% 4.83/1.85  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.83/1.85  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.83/1.85  tff(f_180, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 4.83/1.85  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.83/1.85  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.83/1.85  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 4.83/1.85  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 4.83/1.85  tff(c_34, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_28, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_86, plain, (![B_155, A_156]: (v2_pre_topc(B_155) | ~m1_pre_topc(B_155, A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/1.85  tff(c_95, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_86])).
% 4.83/1.85  tff(c_110, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_95])).
% 4.83/1.85  tff(c_55, plain, (![B_153, A_154]: (l1_pre_topc(B_153) | ~m1_pre_topc(B_153, A_154) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.83/1.85  tff(c_64, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_55])).
% 4.83/1.85  tff(c_77, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_64])).
% 4.83/1.85  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_117, plain, (![C_157, A_158, B_159]: (m1_pre_topc(C_157, A_158) | ~m1_pre_topc(C_157, B_159) | ~m1_pre_topc(B_159, A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.83/1.85  tff(c_131, plain, (![A_158]: (m1_pre_topc('#skF_5', A_158) | ~m1_pre_topc('#skF_4', A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158))), inference(resolution, [status(thm)], [c_28, c_117])).
% 4.83/1.85  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_32, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_24, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_359, plain, (![E_198, C_199, D_195, B_197, A_196]: (k3_tmap_1(A_196, B_197, C_199, D_195, E_198)=k2_partfun1(u1_struct_0(C_199), u1_struct_0(B_197), E_198, u1_struct_0(D_195)) | ~m1_pre_topc(D_195, C_199) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_199), u1_struct_0(B_197)))) | ~v1_funct_2(E_198, u1_struct_0(C_199), u1_struct_0(B_197)) | ~v1_funct_1(E_198) | ~m1_pre_topc(D_195, A_196) | ~m1_pre_topc(C_199, A_196) | ~l1_pre_topc(B_197) | ~v2_pre_topc(B_197) | v2_struct_0(B_197) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.83/1.85  tff(c_363, plain, (![A_196, D_195]: (k3_tmap_1(A_196, '#skF_2', '#skF_3', D_195, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_195)) | ~m1_pre_topc(D_195, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_195, A_196) | ~m1_pre_topc('#skF_3', A_196) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_22, c_359])).
% 4.83/1.85  tff(c_367, plain, (![A_196, D_195]: (k3_tmap_1(A_196, '#skF_2', '#skF_3', D_195, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_195)) | ~m1_pre_topc(D_195, '#skF_3') | ~m1_pre_topc(D_195, A_196) | ~m1_pre_topc('#skF_3', A_196) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_26, c_24, c_363])).
% 4.83/1.85  tff(c_370, plain, (![A_205, D_206]: (k3_tmap_1(A_205, '#skF_2', '#skF_3', D_206, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_206)) | ~m1_pre_topc(D_206, '#skF_3') | ~m1_pre_topc(D_206, A_205) | ~m1_pre_topc('#skF_3', A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_48, c_367])).
% 4.83/1.85  tff(c_386, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_370])).
% 4.83/1.85  tff(c_408, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_386])).
% 4.83/1.85  tff(c_409, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_408])).
% 4.83/1.85  tff(c_489, plain, (~m1_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_409])).
% 4.83/1.85  tff(c_507, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_131, c_489])).
% 4.83/1.85  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_77, c_30, c_507])).
% 4.83/1.85  tff(c_516, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_409])).
% 4.83/1.85  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_89, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_86])).
% 4.83/1.85  tff(c_104, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_89])).
% 4.83/1.85  tff(c_58, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_55])).
% 4.83/1.85  tff(c_73, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58])).
% 4.83/1.85  tff(c_378, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_370])).
% 4.83/1.85  tff(c_392, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_30, c_378])).
% 4.83/1.85  tff(c_393, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_392])).
% 4.83/1.85  tff(c_283, plain, (![A_176, B_177, C_178, D_179]: (k2_partfun1(u1_struct_0(A_176), u1_struct_0(B_177), C_178, u1_struct_0(D_179))=k2_tmap_1(A_176, B_177, C_178, D_179) | ~m1_pre_topc(D_179, A_176) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176), u1_struct_0(B_177)))) | ~v1_funct_2(C_178, u1_struct_0(A_176), u1_struct_0(B_177)) | ~v1_funct_1(C_178) | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.85  tff(c_285, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_179))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_179) | ~m1_pre_topc(D_179, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_283])).
% 4.83/1.85  tff(c_288, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_179))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_179) | ~m1_pre_topc(D_179, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_77, c_46, c_44, c_26, c_24, c_285])).
% 4.83/1.85  tff(c_289, plain, (![D_179]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_179))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_179) | ~m1_pre_topc(D_179, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_48, c_288])).
% 4.83/1.85  tff(c_413, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_289])).
% 4.83/1.85  tff(c_420, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_413])).
% 4.83/1.85  tff(c_177, plain, (![E_166, A_165, D_167, B_168, C_164]: (v1_funct_1(k3_tmap_1(A_165, B_168, C_164, D_167, E_166)) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_164), u1_struct_0(B_168)))) | ~v1_funct_2(E_166, u1_struct_0(C_164), u1_struct_0(B_168)) | ~v1_funct_1(E_166) | ~m1_pre_topc(D_167, A_165) | ~m1_pre_topc(C_164, A_165) | ~l1_pre_topc(B_168) | ~v2_pre_topc(B_168) | v2_struct_0(B_168) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.83/1.85  tff(c_179, plain, (![A_165, D_167]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_3', D_167, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_167, A_165) | ~m1_pre_topc('#skF_3', A_165) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_22, c_177])).
% 4.83/1.85  tff(c_182, plain, (![A_165, D_167]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_3', D_167, '#skF_6')) | ~m1_pre_topc(D_167, A_165) | ~m1_pre_topc('#skF_3', A_165) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_26, c_24, c_179])).
% 4.83/1.85  tff(c_183, plain, (![A_165, D_167]: (v1_funct_1(k3_tmap_1(A_165, '#skF_2', '#skF_3', D_167, '#skF_6')) | ~m1_pre_topc(D_167, A_165) | ~m1_pre_topc('#skF_3', A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_48, c_182])).
% 4.83/1.85  tff(c_435, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_183])).
% 4.83/1.85  tff(c_445, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_36, c_435])).
% 4.83/1.85  tff(c_446, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_445])).
% 4.83/1.85  tff(c_341, plain, (![E_185, D_186, C_183, A_184, B_187]: (v1_funct_2(k3_tmap_1(A_184, B_187, C_183, D_186, E_185), u1_struct_0(D_186), u1_struct_0(B_187)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183), u1_struct_0(B_187)))) | ~v1_funct_2(E_185, u1_struct_0(C_183), u1_struct_0(B_187)) | ~v1_funct_1(E_185) | ~m1_pre_topc(D_186, A_184) | ~m1_pre_topc(C_183, A_184) | ~l1_pre_topc(B_187) | ~v2_pre_topc(B_187) | v2_struct_0(B_187) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.83/1.85  tff(c_343, plain, (![A_184, D_186]: (v1_funct_2(k3_tmap_1(A_184, '#skF_2', '#skF_3', D_186, '#skF_6'), u1_struct_0(D_186), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_186, A_184) | ~m1_pre_topc('#skF_3', A_184) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_22, c_341])).
% 4.83/1.85  tff(c_346, plain, (![A_184, D_186]: (v1_funct_2(k3_tmap_1(A_184, '#skF_2', '#skF_3', D_186, '#skF_6'), u1_struct_0(D_186), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_186, A_184) | ~m1_pre_topc('#skF_3', A_184) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_26, c_24, c_343])).
% 4.83/1.85  tff(c_347, plain, (![A_184, D_186]: (v1_funct_2(k3_tmap_1(A_184, '#skF_2', '#skF_3', D_186, '#skF_6'), u1_struct_0(D_186), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_186, A_184) | ~m1_pre_topc('#skF_3', A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(negUnitSimplification, [status(thm)], [c_48, c_346])).
% 4.83/1.85  tff(c_432, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_347])).
% 4.83/1.85  tff(c_442, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_36, c_432])).
% 4.83/1.85  tff(c_443, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_442])).
% 4.83/1.85  tff(c_10, plain, (![A_53, D_56, E_57, C_55, B_54]: (m1_subset_1(k3_tmap_1(A_53, B_54, C_55, D_56, E_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56), u1_struct_0(B_54)))) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55), u1_struct_0(B_54)))) | ~v1_funct_2(E_57, u1_struct_0(C_55), u1_struct_0(B_54)) | ~v1_funct_1(E_57) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc(C_55, A_53) | ~l1_pre_topc(B_54) | ~v2_pre_topc(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.83/1.85  tff(c_429, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_10])).
% 4.83/1.85  tff(c_439, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_44, c_40, c_36, c_26, c_24, c_22, c_429])).
% 4.83/1.85  tff(c_440, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_439])).
% 4.83/1.85  tff(c_6, plain, (![A_7, B_15, C_19, D_21]: (k2_partfun1(u1_struct_0(A_7), u1_struct_0(B_15), C_19, u1_struct_0(D_21))=k2_tmap_1(A_7, B_15, C_19, D_21) | ~m1_pre_topc(D_21, A_7) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7), u1_struct_0(B_15)))) | ~v1_funct_2(C_19, u1_struct_0(A_7), u1_struct_0(B_15)) | ~v1_funct_1(C_19) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.83/1.85  tff(c_454, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_440, c_6])).
% 4.83/1.85  tff(c_467, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_73, c_46, c_44, c_446, c_443, c_454])).
% 4.83/1.85  tff(c_468, plain, (![D_21]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_21))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_21) | ~m1_pre_topc(D_21, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_48, c_467])).
% 4.83/1.85  tff(c_8, plain, (![C_46, B_38, E_52, D_50, A_22]: (k3_tmap_1(A_22, B_38, C_46, D_50, E_52)=k2_partfun1(u1_struct_0(C_46), u1_struct_0(B_38), E_52, u1_struct_0(D_50)) | ~m1_pre_topc(D_50, C_46) | ~m1_subset_1(E_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_46), u1_struct_0(B_38)))) | ~v1_funct_2(E_52, u1_struct_0(C_46), u1_struct_0(B_38)) | ~v1_funct_1(E_52) | ~m1_pre_topc(D_50, A_22) | ~m1_pre_topc(C_46, A_22) | ~l1_pre_topc(B_38) | ~v2_pre_topc(B_38) | v2_struct_0(B_38) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.83/1.85  tff(c_450, plain, (![A_22, D_50]: (k3_tmap_1(A_22, '#skF_2', '#skF_4', D_50, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_50)) | ~m1_pre_topc(D_50, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')) | ~m1_pre_topc(D_50, A_22) | ~m1_pre_topc('#skF_4', A_22) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_440, c_8])).
% 4.83/1.85  tff(c_459, plain, (![A_22, D_50]: (k3_tmap_1(A_22, '#skF_2', '#skF_4', D_50, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_50)) | ~m1_pre_topc(D_50, '#skF_4') | ~m1_pre_topc(D_50, A_22) | ~m1_pre_topc('#skF_4', A_22) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_446, c_443, c_450])).
% 4.83/1.85  tff(c_844, plain, (![A_249, D_250]: (k3_tmap_1(A_249, '#skF_2', '#skF_4', D_250, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), u1_struct_0(D_250)) | ~m1_pre_topc(D_250, '#skF_4') | ~m1_pre_topc(D_250, A_249) | ~m1_pre_topc('#skF_4', A_249) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(negUnitSimplification, [status(thm)], [c_48, c_459])).
% 4.83/1.85  tff(c_1417, plain, (![A_285, D_286]: (k3_tmap_1(A_285, '#skF_2', '#skF_4', D_286, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_286) | ~m1_pre_topc(D_286, '#skF_4') | ~m1_pre_topc(D_286, A_285) | ~m1_pre_topc('#skF_4', A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~m1_pre_topc(D_286, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_844])).
% 4.83/1.85  tff(c_16, plain, (![A_58, E_88, B_74, D_86, C_82]: (r2_funct_2(u1_struct_0(C_82), u1_struct_0(B_74), k3_tmap_1(A_58, B_74, D_86, C_82, k2_tmap_1(A_58, B_74, E_88, D_86)), k2_tmap_1(A_58, B_74, E_88, C_82)) | ~m1_pre_topc(C_82, D_86) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(B_74)))) | ~v1_funct_2(E_88, u1_struct_0(A_58), u1_struct_0(B_74)) | ~v1_funct_1(E_88) | ~m1_pre_topc(D_86, A_58) | v2_struct_0(D_86) | ~m1_pre_topc(C_82, A_58) | v2_struct_0(C_82) | ~l1_pre_topc(B_74) | ~v2_pre_topc(B_74) | v2_struct_0(B_74) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.83/1.85  tff(c_1448, plain, (![D_286]: (r2_funct_2(u1_struct_0(D_286), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_286), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_286)) | ~m1_pre_topc(D_286, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc(D_286, '#skF_3') | v2_struct_0(D_286) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_286, '#skF_4') | ~m1_pre_topc(D_286, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_286, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1417, c_16])).
% 4.83/1.85  tff(c_1471, plain, (![D_286]: (r2_funct_2(u1_struct_0(D_286), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_286), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_286)) | v2_struct_0('#skF_4') | v2_struct_0(D_286) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_286, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_286, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_77, c_30, c_110, c_77, c_46, c_44, c_30, c_26, c_24, c_22, c_1448])).
% 4.83/1.85  tff(c_1477, plain, (![D_287]: (r2_funct_2(u1_struct_0(D_287), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), D_287), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_287)) | v2_struct_0(D_287) | ~m1_pre_topc(D_287, '#skF_3') | ~m1_pre_topc(D_287, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_48, c_38, c_1471])).
% 4.83/1.85  tff(c_515, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_409])).
% 4.83/1.85  tff(c_597, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_515, c_289])).
% 4.83/1.85  tff(c_604, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_597])).
% 4.83/1.85  tff(c_20, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.83/1.85  tff(c_425, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_20])).
% 4.83/1.85  tff(c_767, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_425])).
% 4.83/1.85  tff(c_1439, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1417, c_767])).
% 4.83/1.85  tff(c_1462, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_52, c_50, c_36, c_32, c_28, c_1439])).
% 4.83/1.85  tff(c_1463, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1462])).
% 4.83/1.85  tff(c_1480, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1477, c_1463])).
% 4.83/1.85  tff(c_1483, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_516, c_1480])).
% 4.83/1.85  tff(c_1485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1483])).
% 4.83/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  
% 4.83/1.85  Inference rules
% 4.83/1.85  ----------------------
% 4.83/1.85  #Ref     : 0
% 4.83/1.85  #Sup     : 277
% 4.83/1.85  #Fact    : 0
% 4.83/1.85  #Define  : 0
% 4.83/1.85  #Split   : 8
% 4.83/1.85  #Chain   : 0
% 4.83/1.85  #Close   : 0
% 4.83/1.85  
% 4.83/1.85  Ordering : KBO
% 4.83/1.85  
% 4.83/1.85  Simplification rules
% 4.83/1.85  ----------------------
% 4.83/1.85  #Subsume      : 71
% 4.83/1.85  #Demod        : 726
% 4.83/1.85  #Tautology    : 74
% 4.83/1.85  #SimpNegUnit  : 104
% 4.83/1.85  #BackRed      : 3
% 4.83/1.85  
% 4.83/1.85  #Partial instantiations: 0
% 4.83/1.85  #Strategies tried      : 1
% 4.83/1.85  
% 4.83/1.85  Timing (in seconds)
% 4.83/1.85  ----------------------
% 4.83/1.85  Preprocessing        : 0.34
% 4.83/1.85  Parsing              : 0.18
% 4.83/1.85  CNF conversion       : 0.04
% 4.83/1.85  Main loop            : 0.69
% 4.83/1.85  Inferencing          : 0.22
% 4.83/1.85  Reduction            : 0.25
% 4.83/1.85  Demodulation         : 0.19
% 4.83/1.85  BG Simplification    : 0.03
% 4.83/1.85  Subsumption          : 0.17
% 4.83/1.86  Abstraction          : 0.04
% 4.83/1.86  MUC search           : 0.00
% 4.83/1.86  Cooper               : 0.00
% 4.83/1.86  Total                : 1.08
% 4.83/1.86  Index Insertion      : 0.00
% 4.83/1.86  Index Deletion       : 0.00
% 4.83/1.86  Index Matching       : 0.00
% 4.83/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
