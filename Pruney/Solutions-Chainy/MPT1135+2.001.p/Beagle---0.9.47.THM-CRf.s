%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:17 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 374 expanded)
%              Number of leaves         :   25 ( 139 expanded)
%              Depth                    :   16
%              Number of atoms          :  165 ( 964 expanded)
%              Number of equality atoms :   37 ( 259 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))
               => ( B = C
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(A,B)),u1_pre_topc(k1_pre_topc(A,B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_47,plain,(
    ! [A_45,B_46] :
      ( v1_pre_topc(g1_pre_topc(A_45,B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_16] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_47])).

tff(c_26,plain,(
    '#skF_2' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_33,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_87,plain,(
    ! [A_51,B_52] :
      ( m1_pre_topc(k1_pre_topc(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_87])).

tff(c_95,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_109,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_112,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_76,plain,(
    ! [A_49,B_50] :
      ( v1_pre_topc(k1_pre_topc(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_76])).

tff(c_86,plain,(
    v1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_82])).

tff(c_96,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0(k1_pre_topc(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_102,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_96])).

tff(c_106,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,
    ( g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_144,plain,(
    g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_86,c_125])).

tff(c_24,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_24])).

tff(c_113,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_34])).

tff(c_270,plain,(
    k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') != k1_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_113])).

tff(c_41,plain,(
    ! [A_42,B_43] :
      ( l1_pre_topc(g1_pre_topc(A_42,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    ! [A_16] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_16),u1_pre_topc(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_83,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_152,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_152])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_166,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_285,plain,(
    ! [A_61,B_62] :
      ( k2_struct_0(k1_pre_topc(A_61,B_62)) = B_62
      | ~ m1_pre_topc(k1_pre_topc(A_61,B_62),A_61)
      | ~ v1_pre_topc(k1_pre_topc(A_61,B_62))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_289,plain,
    ( k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95,c_285])).

tff(c_295,plain,(
    k2_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_33,c_86,c_289])).

tff(c_4,plain,(
    ! [A_2,C_8] :
      ( k1_pre_topc(A_2,k2_struct_0(C_8)) = C_8
      | ~ m1_pre_topc(C_8,A_2)
      | ~ v1_pre_topc(C_8)
      | ~ m1_subset_1(k2_struct_0(C_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_299,plain,(
    ! [A_2] :
      ( k1_pre_topc(A_2,k2_struct_0(k1_pre_topc('#skF_1','#skF_3'))) = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_2)
      | ~ v1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_4])).

tff(c_366,plain,(
    ! [A_65] :
      ( k1_pre_topc(A_65,'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_65)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_295,c_299])).

tff(c_378,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_366])).

tff(c_388,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_3') = k1_pre_topc('#skF_1','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_378])).

tff(c_389,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_388])).

tff(c_399,plain,(
    ! [D_66,B_67,C_68,A_69] :
      ( m1_pre_topc(D_66,B_67)
      | ~ m1_pre_topc(C_68,A_69)
      | g1_pre_topc(u1_struct_0(D_66),u1_pre_topc(D_66)) != g1_pre_topc(u1_struct_0(C_68),u1_pre_topc(C_68))
      | g1_pre_topc(u1_struct_0(B_67),u1_pre_topc(B_67)) != g1_pre_topc(u1_struct_0(A_69),u1_pre_topc(A_69))
      | ~ l1_pre_topc(D_66)
      | ~ l1_pre_topc(C_68)
      | ~ l1_pre_topc(B_67)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_405,plain,(
    ! [D_66,B_67] :
      ( m1_pre_topc(D_66,B_67)
      | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')),u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != g1_pre_topc(u1_struct_0(D_66),u1_pre_topc(D_66))
      | g1_pre_topc(u1_struct_0(B_67),u1_pre_topc(B_67)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_66)
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc(B_67)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_95,c_399])).

tff(c_593,plain,(
    ! [D_82,B_83] :
      ( m1_pre_topc(D_82,B_83)
      | g1_pre_topc(u1_struct_0(D_82),u1_pre_topc(D_82)) != k1_pre_topc('#skF_1','#skF_3')
      | g1_pre_topc(u1_struct_0(B_83),u1_pre_topc(B_83)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_82)
      | ~ l1_pre_topc(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_112,c_144,c_106,c_405])).

tff(c_603,plain,(
    ! [B_83] :
      ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_83)
      | g1_pre_topc('#skF_3',u1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))) != k1_pre_topc('#skF_1','#skF_3')
      | g1_pre_topc(u1_struct_0(B_83),u1_pre_topc(B_83)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_593])).

tff(c_615,plain,(
    ! [B_84] :
      ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),B_84)
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_144,c_603])).

tff(c_633,plain,(
    ! [A_1] :
      ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),A_1)
      | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != A_1
      | ~ l1_pre_topc(A_1)
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_615])).

tff(c_668,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_633])).

tff(c_670,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_3'),g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_668])).

tff(c_671,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_670])).

tff(c_683,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_671])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  %$ m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.45  
% 2.76/1.45  %Foreground sorts:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Background operators:
% 2.76/1.45  
% 2.76/1.45  
% 2.76/1.45  %Foreground operators:
% 2.76/1.45  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.76/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.76/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.76/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.76/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.45  
% 3.22/1.47  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))) => ((B = C) => (g1_pre_topc(u1_struct_0(k1_pre_topc(A, B)), u1_pre_topc(k1_pre_topc(A, B))) = k1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_pre_topc)).
% 3.22/1.47  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.22/1.47  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 3.22/1.47  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.22/1.47  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.47  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.22/1.47  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.22/1.47  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 3.22/1.47  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 3.22/1.47  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.47  tff(c_18, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.47  tff(c_47, plain, (![A_45, B_46]: (v1_pre_topc(g1_pre_topc(A_45, B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.47  tff(c_51, plain, (![A_16]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_47])).
% 3.22/1.47  tff(c_26, plain, ('#skF_2'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.47  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.47  tff(c_33, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.22/1.47  tff(c_87, plain, (![A_51, B_52]: (m1_pre_topc(k1_pre_topc(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.47  tff(c_91, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_87])).
% 3.22/1.47  tff(c_95, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 3.22/1.47  tff(c_16, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.47  tff(c_109, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_16])).
% 3.22/1.47  tff(c_112, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_109])).
% 3.22/1.47  tff(c_76, plain, (![A_49, B_50]: (v1_pre_topc(k1_pre_topc(A_49, B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.47  tff(c_82, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_76])).
% 3.22/1.47  tff(c_86, plain, (v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_82])).
% 3.22/1.47  tff(c_96, plain, (![A_53, B_54]: (u1_struct_0(k1_pre_topc(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.22/1.47  tff(c_102, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_33, c_96])).
% 3.22/1.47  tff(c_106, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_102])).
% 3.22/1.47  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.47  tff(c_125, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 3.22/1.47  tff(c_144, plain, (g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_86, c_125])).
% 3.22/1.47  tff(c_24, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.47  tff(c_34, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_24])).
% 3.22/1.47  tff(c_113, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_34])).
% 3.22/1.47  tff(c_270, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')!=k1_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_113])).
% 3.22/1.47  tff(c_41, plain, (![A_42, B_43]: (l1_pre_topc(g1_pre_topc(A_42, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.47  tff(c_45, plain, (![A_16]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_16), u1_pre_topc(A_16))) | ~l1_pre_topc(A_16))), inference(resolution, [status(thm)], [c_18, c_41])).
% 3.22/1.47  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.22/1.47  tff(c_83, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_76])).
% 3.22/1.47  tff(c_152, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_83])).
% 3.22/1.47  tff(c_158, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_45, c_152])).
% 3.22/1.47  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_158])).
% 3.22/1.47  tff(c_166, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_83])).
% 3.22/1.47  tff(c_285, plain, (![A_61, B_62]: (k2_struct_0(k1_pre_topc(A_61, B_62))=B_62 | ~m1_pre_topc(k1_pre_topc(A_61, B_62), A_61) | ~v1_pre_topc(k1_pre_topc(A_61, B_62)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.47  tff(c_289, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95, c_285])).
% 3.22/1.47  tff(c_295, plain, (k2_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_33, c_86, c_289])).
% 3.22/1.47  tff(c_4, plain, (![A_2, C_8]: (k1_pre_topc(A_2, k2_struct_0(C_8))=C_8 | ~m1_pre_topc(C_8, A_2) | ~v1_pre_topc(C_8) | ~m1_subset_1(k2_struct_0(C_8), k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.47  tff(c_299, plain, (![A_2]: (k1_pre_topc(A_2, k2_struct_0(k1_pre_topc('#skF_1', '#skF_3')))=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_2) | ~v1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(superposition, [status(thm), theory('equality')], [c_295, c_4])).
% 3.22/1.47  tff(c_366, plain, (![A_65]: (k1_pre_topc(A_65, '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_65) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_295, c_299])).
% 3.22/1.47  tff(c_378, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_366])).
% 3.22/1.47  tff(c_388, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_3')=k1_pre_topc('#skF_1', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_378])).
% 3.22/1.47  tff(c_389, plain, (~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_270, c_388])).
% 3.22/1.47  tff(c_399, plain, (![D_66, B_67, C_68, A_69]: (m1_pre_topc(D_66, B_67) | ~m1_pre_topc(C_68, A_69) | g1_pre_topc(u1_struct_0(D_66), u1_pre_topc(D_66))!=g1_pre_topc(u1_struct_0(C_68), u1_pre_topc(C_68)) | g1_pre_topc(u1_struct_0(B_67), u1_pre_topc(B_67))!=g1_pre_topc(u1_struct_0(A_69), u1_pre_topc(A_69)) | ~l1_pre_topc(D_66) | ~l1_pre_topc(C_68) | ~l1_pre_topc(B_67) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.47  tff(c_405, plain, (![D_66, B_67]: (m1_pre_topc(D_66, B_67) | g1_pre_topc(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')), u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=g1_pre_topc(u1_struct_0(D_66), u1_pre_topc(D_66)) | g1_pre_topc(u1_struct_0(B_67), u1_pre_topc(B_67))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_66) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(B_67) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_95, c_399])).
% 3.22/1.47  tff(c_593, plain, (![D_82, B_83]: (m1_pre_topc(D_82, B_83) | g1_pre_topc(u1_struct_0(D_82), u1_pre_topc(D_82))!=k1_pre_topc('#skF_1', '#skF_3') | g1_pre_topc(u1_struct_0(B_83), u1_pre_topc(B_83))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_82) | ~l1_pre_topc(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_112, c_144, c_106, c_405])).
% 3.22/1.47  tff(c_603, plain, (![B_83]: (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_83) | g1_pre_topc('#skF_3', u1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')))!=k1_pre_topc('#skF_1', '#skF_3') | g1_pre_topc(u1_struct_0(B_83), u1_pre_topc(B_83))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc(B_83))), inference(superposition, [status(thm), theory('equality')], [c_106, c_593])).
% 3.22/1.47  tff(c_615, plain, (![B_84]: (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), B_84) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_144, c_603])).
% 3.22/1.47  tff(c_633, plain, (![A_1]: (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), A_1) | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=A_1 | ~l1_pre_topc(A_1) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_615])).
% 3.22/1.47  tff(c_668, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(reflexivity, [status(thm), theory('equality')], [c_633])).
% 3.22/1.47  tff(c_670, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_3'), g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_668])).
% 3.22/1.47  tff(c_671, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_389, c_670])).
% 3.22/1.47  tff(c_683, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51, c_671])).
% 3.22/1.47  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_683])).
% 3.22/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  Inference rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Ref     : 2
% 3.22/1.47  #Sup     : 145
% 3.22/1.47  #Fact    : 0
% 3.22/1.47  #Define  : 0
% 3.22/1.47  #Split   : 3
% 3.22/1.47  #Chain   : 0
% 3.22/1.47  #Close   : 0
% 3.22/1.47  
% 3.22/1.47  Ordering : KBO
% 3.22/1.47  
% 3.22/1.47  Simplification rules
% 3.22/1.47  ----------------------
% 3.22/1.47  #Subsume      : 23
% 3.22/1.47  #Demod        : 130
% 3.22/1.47  #Tautology    : 40
% 3.22/1.47  #SimpNegUnit  : 3
% 3.22/1.47  #BackRed      : 5
% 3.22/1.47  
% 3.22/1.47  #Partial instantiations: 0
% 3.22/1.47  #Strategies tried      : 1
% 3.22/1.47  
% 3.22/1.47  Timing (in seconds)
% 3.22/1.47  ----------------------
% 3.22/1.47  Preprocessing        : 0.32
% 3.22/1.47  Parsing              : 0.17
% 3.22/1.47  CNF conversion       : 0.02
% 3.22/1.47  Main loop            : 0.38
% 3.22/1.47  Inferencing          : 0.13
% 3.22/1.47  Reduction            : 0.13
% 3.22/1.47  Demodulation         : 0.09
% 3.22/1.47  BG Simplification    : 0.02
% 3.22/1.47  Subsumption          : 0.08
% 3.22/1.47  Abstraction          : 0.02
% 3.22/1.47  MUC search           : 0.00
% 3.22/1.47  Cooper               : 0.00
% 3.22/1.47  Total                : 0.73
% 3.22/1.47  Index Insertion      : 0.00
% 3.22/1.47  Index Deletion       : 0.00
% 3.22/1.47  Index Matching       : 0.00
% 3.22/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
