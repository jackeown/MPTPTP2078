%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:57 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 232 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 914 expanded)
%              Number of equality atoms :   39 ( 245 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( C = u1_struct_0(B)
                   => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10,plain,(
    ! [A_23,B_24] :
      ( l1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( v1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [A_23,B_24] :
      ( v2_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_155,plain,(
    ! [A_69,B_70] :
      ( k6_tmap_1(A_69,u1_struct_0(B_70)) = k8_tmap_1(A_69,B_70)
      | ~ m1_subset_1(u1_struct_0(B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(k8_tmap_1(A_69,B_70))
      | ~ v2_pre_topc(k8_tmap_1(A_69,B_70))
      | ~ v1_pre_topc(k8_tmap_1(A_69,B_70))
      | ~ m1_pre_topc(B_70,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [A_71,B_72] :
      ( k6_tmap_1(A_71,u1_struct_0(B_72)) = k8_tmap_1(A_71,B_72)
      | ~ l1_pre_topc(k8_tmap_1(A_71,B_72))
      | ~ v2_pre_topc(k8_tmap_1(A_71,B_72))
      | ~ v1_pre_topc(k8_tmap_1(A_71,B_72))
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71)
      | ~ m1_pre_topc(B_72,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_177,plain,(
    ! [A_73,B_74] :
      ( k6_tmap_1(A_73,u1_struct_0(B_74)) = k8_tmap_1(A_73,B_74)
      | ~ l1_pre_topc(k8_tmap_1(A_73,B_74))
      | ~ v1_pre_topc(k8_tmap_1(A_73,B_74))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_182,plain,(
    ! [A_75,B_76] :
      ( k6_tmap_1(A_75,u1_struct_0(B_76)) = k8_tmap_1(A_75,B_76)
      | ~ l1_pre_topc(k8_tmap_1(A_75,B_76))
      | ~ m1_pre_topc(B_76,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_14,c_177])).

tff(c_187,plain,(
    ! [A_77,B_78] :
      ( k6_tmap_1(A_77,u1_struct_0(B_78)) = k8_tmap_1(A_77,B_78)
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_42,plain,(
    ! [A_43,B_44] :
      ( u1_struct_0(k6_tmap_1(A_43,B_44)) = u1_struct_0(A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [A_28,B_30] :
      ( u1_struct_0(k6_tmap_1(A_28,u1_struct_0(B_30))) = u1_struct_0(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_212,plain,(
    ! [A_79,B_80] :
      ( u1_struct_0(k8_tmap_1(A_79,B_80)) = u1_struct_0(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_46])).

tff(c_34,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_37,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_246,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_37])).

tff(c_253,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_246])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_253])).

tff(c_257,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_267,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_36])).

tff(c_457,plain,(
    ! [A_97,B_98] :
      ( u1_pre_topc(k6_tmap_1(A_97,B_98)) = k5_tmap_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_478,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_267,c_457])).

tff(c_494,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_478])).

tff(c_495,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) = k5_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_494])).

tff(c_268,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(u1_struct_0(B_81),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_274,plain,(
    ! [B_81] :
      ( m1_subset_1(u1_struct_0(B_81),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_81,k8_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_268])).

tff(c_302,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_334,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_302])).

tff(c_337,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_334])).

tff(c_339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_337])).

tff(c_341,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_256,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_351,plain,(
    ! [A_94,B_95] :
      ( u1_struct_0(k6_tmap_1(A_94,B_95)) = u1_struct_0(A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_369,plain,(
    ! [B_95] :
      ( u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_2','#skF_3'),B_95)) = u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_351])).

tff(c_385,plain,(
    ! [B_95] :
      ( u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_2','#skF_3'),B_95)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
      | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_257,c_369])).

tff(c_2366,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_2370,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_2366])).

tff(c_2373,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2370])).

tff(c_2375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2373])).

tff(c_2377,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_2217,plain,(
    ! [A_170,B_171] :
      ( k6_tmap_1(A_170,u1_struct_0(B_171)) = k8_tmap_1(A_170,B_171)
      | ~ m1_subset_1(u1_struct_0(B_171),k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(k8_tmap_1(A_170,B_171))
      | ~ v2_pre_topc(k8_tmap_1(A_170,B_171))
      | ~ v1_pre_topc(k8_tmap_1(A_170,B_171))
      | ~ m1_pre_topc(B_171,A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2619,plain,(
    ! [A_184,B_185] :
      ( k6_tmap_1(A_184,u1_struct_0(B_185)) = k8_tmap_1(A_184,B_185)
      | ~ l1_pre_topc(k8_tmap_1(A_184,B_185))
      | ~ v2_pre_topc(k8_tmap_1(A_184,B_185))
      | ~ v1_pre_topc(k8_tmap_1(A_184,B_185))
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_20,c_2217])).

tff(c_2622,plain,
    ( k6_tmap_1('#skF_2',u1_struct_0('#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2377,c_2619])).

tff(c_2628,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_341,c_256,c_2622])).

tff(c_2629,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2628])).

tff(c_2631,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2629])).

tff(c_2634,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_2631])).

tff(c_2637,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_2634])).

tff(c_2639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2637])).

tff(c_2640,plain,(
    k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2629])).

tff(c_32,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4')
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_292,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_32])).

tff(c_2663,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_292])).

tff(c_2668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_2663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.97  
% 5.18/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/1.97  %$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.18/1.97  
% 5.18/1.97  %Foreground sorts:
% 5.18/1.97  
% 5.18/1.97  
% 5.18/1.97  %Background operators:
% 5.18/1.97  
% 5.18/1.97  
% 5.18/1.97  %Foreground operators:
% 5.18/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.18/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.18/1.97  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.18/1.97  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 5.18/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.18/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.18/1.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.18/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.18/1.97  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.18/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.18/1.97  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 5.18/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.18/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.97  
% 5.45/1.99  tff(f_110, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 5.45/1.99  tff(f_66, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 5.45/1.99  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.45/1.99  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 5.45/1.99  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 5.45/1.99  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_10, plain, (![A_23, B_24]: (l1_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.45/1.99  tff(c_14, plain, (![A_23, B_24]: (v1_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.45/1.99  tff(c_12, plain, (![A_23, B_24]: (v2_pre_topc(k8_tmap_1(A_23, B_24)) | ~m1_pre_topc(B_24, A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.45/1.99  tff(c_20, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.45/1.99  tff(c_155, plain, (![A_69, B_70]: (k6_tmap_1(A_69, u1_struct_0(B_70))=k8_tmap_1(A_69, B_70) | ~m1_subset_1(u1_struct_0(B_70), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(k8_tmap_1(A_69, B_70)) | ~v2_pre_topc(k8_tmap_1(A_69, B_70)) | ~v1_pre_topc(k8_tmap_1(A_69, B_70)) | ~m1_pre_topc(B_70, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/1.99  tff(c_172, plain, (![A_71, B_72]: (k6_tmap_1(A_71, u1_struct_0(B_72))=k8_tmap_1(A_71, B_72) | ~l1_pre_topc(k8_tmap_1(A_71, B_72)) | ~v2_pre_topc(k8_tmap_1(A_71, B_72)) | ~v1_pre_topc(k8_tmap_1(A_71, B_72)) | ~v2_pre_topc(A_71) | v2_struct_0(A_71) | ~m1_pre_topc(B_72, A_71) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_20, c_155])).
% 5.45/1.99  tff(c_177, plain, (![A_73, B_74]: (k6_tmap_1(A_73, u1_struct_0(B_74))=k8_tmap_1(A_73, B_74) | ~l1_pre_topc(k8_tmap_1(A_73, B_74)) | ~v1_pre_topc(k8_tmap_1(A_73, B_74)) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(resolution, [status(thm)], [c_12, c_172])).
% 5.45/1.99  tff(c_182, plain, (![A_75, B_76]: (k6_tmap_1(A_75, u1_struct_0(B_76))=k8_tmap_1(A_75, B_76) | ~l1_pre_topc(k8_tmap_1(A_75, B_76)) | ~m1_pre_topc(B_76, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_14, c_177])).
% 5.45/1.99  tff(c_187, plain, (![A_77, B_78]: (k6_tmap_1(A_77, u1_struct_0(B_78))=k8_tmap_1(A_77, B_78) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_10, c_182])).
% 5.45/1.99  tff(c_42, plain, (![A_43, B_44]: (u1_struct_0(k6_tmap_1(A_43, B_44))=u1_struct_0(A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.45/1.99  tff(c_46, plain, (![A_28, B_30]: (u1_struct_0(k6_tmap_1(A_28, u1_struct_0(B_30)))=u1_struct_0(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_20, c_42])).
% 5.45/1.99  tff(c_212, plain, (![A_79, B_80]: (u1_struct_0(k8_tmap_1(A_79, B_80))=u1_struct_0(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(superposition, [status(thm), theory('equality')], [c_187, c_46])).
% 5.45/1.99  tff(c_34, plain, (u1_struct_0('#skF_3')='#skF_4' | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_37, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 5.45/1.99  tff(c_246, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_212, c_37])).
% 5.45/1.99  tff(c_253, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_246])).
% 5.45/1.99  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_253])).
% 5.45/1.99  tff(c_257, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 5.45/1.99  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_267, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_36])).
% 5.45/1.99  tff(c_457, plain, (![A_97, B_98]: (u1_pre_topc(k6_tmap_1(A_97, B_98))=k5_tmap_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.45/1.99  tff(c_478, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_267, c_457])).
% 5.45/1.99  tff(c_494, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_478])).
% 5.45/1.99  tff(c_495, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))=k5_tmap_1('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_494])).
% 5.45/1.99  tff(c_268, plain, (![B_81, A_82]: (m1_subset_1(u1_struct_0(B_81), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.45/1.99  tff(c_274, plain, (![B_81]: (m1_subset_1(u1_struct_0(B_81), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_81, k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_257, c_268])).
% 5.45/1.99  tff(c_302, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_274])).
% 5.45/1.99  tff(c_334, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_302])).
% 5.45/1.99  tff(c_337, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_334])).
% 5.45/1.99  tff(c_339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_337])).
% 5.45/1.99  tff(c_341, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_274])).
% 5.45/1.99  tff(c_256, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 5.45/1.99  tff(c_351, plain, (![A_94, B_95]: (u1_struct_0(k6_tmap_1(A_94, B_95))=u1_struct_0(A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.45/1.99  tff(c_369, plain, (![B_95]: (u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_2', '#skF_3'), B_95))=u1_struct_0(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_257, c_351])).
% 5.45/1.99  tff(c_385, plain, (![B_95]: (u1_struct_0(k6_tmap_1(k8_tmap_1('#skF_2', '#skF_3'), B_95))=u1_struct_0('#skF_2') | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k8_tmap_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_257, c_369])).
% 5.45/1.99  tff(c_2366, plain, (~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_385])).
% 5.45/1.99  tff(c_2370, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_2366])).
% 5.45/1.99  tff(c_2373, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2370])).
% 5.45/1.99  tff(c_2375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2373])).
% 5.45/1.99  tff(c_2377, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_385])).
% 5.45/1.99  tff(c_2217, plain, (![A_170, B_171]: (k6_tmap_1(A_170, u1_struct_0(B_171))=k8_tmap_1(A_170, B_171) | ~m1_subset_1(u1_struct_0(B_171), k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(k8_tmap_1(A_170, B_171)) | ~v2_pre_topc(k8_tmap_1(A_170, B_171)) | ~v1_pre_topc(k8_tmap_1(A_170, B_171)) | ~m1_pre_topc(B_171, A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.45/1.99  tff(c_2619, plain, (![A_184, B_185]: (k6_tmap_1(A_184, u1_struct_0(B_185))=k8_tmap_1(A_184, B_185) | ~l1_pre_topc(k8_tmap_1(A_184, B_185)) | ~v2_pre_topc(k8_tmap_1(A_184, B_185)) | ~v1_pre_topc(k8_tmap_1(A_184, B_185)) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_20, c_2217])).
% 5.45/1.99  tff(c_2622, plain, (k6_tmap_1('#skF_2', u1_struct_0('#skF_3'))=k8_tmap_1('#skF_2', '#skF_3') | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2377, c_2619])).
% 5.45/1.99  tff(c_2628, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_28, c_341, c_256, c_2622])).
% 5.45/1.99  tff(c_2629, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_2628])).
% 5.45/1.99  tff(c_2631, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2629])).
% 5.45/1.99  tff(c_2634, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_2631])).
% 5.45/1.99  tff(c_2637, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_2634])).
% 5.45/1.99  tff(c_2639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2637])).
% 5.45/1.99  tff(c_2640, plain, (k8_tmap_1('#skF_2', '#skF_3')=k6_tmap_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_2629])).
% 5.45/1.99  tff(c_32, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=k5_tmap_1('#skF_2', '#skF_4') | u1_struct_0(k8_tmap_1('#skF_2', '#skF_3'))!=u1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.45/1.99  tff(c_292, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=k5_tmap_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_32])).
% 5.45/1.99  tff(c_2663, plain, (u1_pre_topc(k6_tmap_1('#skF_2', '#skF_4'))!=k5_tmap_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_292])).
% 5.45/1.99  tff(c_2668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_2663])).
% 5.45/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/1.99  
% 5.45/1.99  Inference rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Ref     : 0
% 5.45/1.99  #Sup     : 663
% 5.45/1.99  #Fact    : 0
% 5.45/1.99  #Define  : 0
% 5.45/1.99  #Split   : 23
% 5.45/1.99  #Chain   : 0
% 5.45/1.99  #Close   : 0
% 5.45/1.99  
% 5.45/1.99  Ordering : KBO
% 5.45/1.99  
% 5.45/1.99  Simplification rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Subsume      : 154
% 5.45/1.99  #Demod        : 306
% 5.45/1.99  #Tautology    : 144
% 5.45/1.99  #SimpNegUnit  : 82
% 5.45/1.99  #BackRed      : 44
% 5.45/1.99  
% 5.45/1.99  #Partial instantiations: 0
% 5.45/1.99  #Strategies tried      : 1
% 5.45/1.99  
% 5.45/1.99  Timing (in seconds)
% 5.45/1.99  ----------------------
% 5.45/1.99  Preprocessing        : 0.34
% 5.45/1.99  Parsing              : 0.17
% 5.45/1.99  CNF conversion       : 0.03
% 5.45/1.99  Main loop            : 0.87
% 5.45/1.99  Inferencing          : 0.29
% 5.45/1.99  Reduction            : 0.26
% 5.45/1.99  Demodulation         : 0.18
% 5.45/1.99  BG Simplification    : 0.05
% 5.45/1.99  Subsumption          : 0.22
% 5.45/1.99  Abstraction          : 0.05
% 5.45/1.99  MUC search           : 0.00
% 5.45/1.99  Cooper               : 0.00
% 5.45/1.99  Total                : 1.24
% 5.45/1.99  Index Insertion      : 0.00
% 5.45/1.99  Index Deletion       : 0.00
% 5.45/1.99  Index Matching       : 0.00
% 5.45/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
